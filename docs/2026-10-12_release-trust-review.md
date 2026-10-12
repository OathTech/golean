# Additional release trust review — 2026-10-12

Reviewed `main` at **`d92b95fdbe5c43c449d7023ba5344ac271211570`**.
Worktree: `.claude/worktrees/release-trust-audit-1012`; branch:
`audit/release-trust-1012`.

**Verdict: two additional release-blocking findings, plus two existing
wrong-answer defects missing from the release punch list.** The strongest new
finding is a race-free, integer-valued Go behavior absent from both GoLean
enumerators. The other is an oracle transformation that changes package
initialization. There are also two smaller tooling/documentation findings.
Severity and proposed dispositions below are the reviewer's assessments, not
user rulings.

Decisions:

- [USER] 2026-10-12: investigate additional release problems and write the review
  in an isolated worktree, avoiding the existing workers.
- [AGENT] 2026-10-12: keep this branch findings-only. Record self-contained
  reproductions here; leave fixes, bug-number allocation, baseline changes and
  the active workers' documents to the release coordinator. Distinguish new
  findings from rediscovered, already-recorded defects.

## Findings

| ID | Priority | Classification | Finding |
|---|---|---|---|
| F1 | P1 / release blocker | New concrete semantic counterexample | Concurrent channel-length reads cannot observe an intervening send |
| F2 | P1 / release blocker | New oracle correctness defect | Harness import pruning deletes initialization effects |
| R1 | P1 / release blocker | Already known; missing from punch list | `uintptr` and `uint64` collapse at runtime type identity |
| R2 | P1 / release blocker | Already known FR-30; missing from punch list | Concurrent print sequences omit legal interleavings |
| F3 | P2 | CLI contract / in-flight documentation | Dedup silently ignores observation and path caps advertised as enforced |
| F4 | P2 | Runner robustness | The depth tracer's timeout bypasses timeout validation |

### F1 — `len(channel)` is observable shared state without a scheduling boundary

Source shape (complete runnable reproduction below):

```go
c := make(chan int, 1)
go func() { c <- 1 }()
a := len(c)
_ = delay(100) // finite pure recursion, no loops or synchronization
b := len(c)
<-c
return 10*a + b
```

**Measured:** pinned gc `go1.26.5 linux/amd64`, `GOMAXPROCS=2`, `-race`,
10,000 calls: `0` 9,674 times; **`1` 326 times**; `11` zero times. Exit 0,
no race diagnostic. A plain run returned `0` on all 10,000 calls; this is a
scheduling-sensitive witness, not a claim that every draw exposes the bug.

GoLean's DFS and dedup engines both exit 0 with exactly **`{0,11}`**. Dedup
reports `certified=checkCert`, 18,121 nodes / 18,129 edges. DFS reports 18,368
steps / 99 probes / 34 leaves. Neither emits a refusal. Removing the delay
still gives the same two-member model; the delay only makes Go exhibit the
missing member more readily. All goroutines are joined through the channel.

**Cause:** `GoLean/GoCore/Multi.lean:420`, `Config.atBoundary`, has no boundary
for the channel branch of `lengthOf` (`Machine.lean:619`). After the post-spawn
boundary clears, both length reads execute before the next scheduling point at
the receive. A peer send cannot occur between them. Ordinary recursive calls
do not open a boundary either. `Ops.lean:2929` correctly treats channel-length
reads as uninstrumented by the data-race checker, but that does not make them
private or commuting operations for scheduling reduction.

The [Go channel contract](https://go.dev/ref/spec#Channel_types) permits `len`
and sends from different goroutines without additional synchronization. This
is therefore a missing **race-free scalar result**, not a race that the model
may legitimately refuse. The checker certifies the modeled machine correctly;
this is not a contradiction of its theorem. The modeled scheduling relation
is too narrow for Go.

**Existing-record check:** `NPDRF.lean` obstruction 5 warns generally about
unrecorded shared reads and movers. The latitude inventory's detector U2 says
channel `len`/`cap` are uninstrumented. Neither supplies this counterexample or
an admission guard. Inventory U-5 / BUG-002 discuss wide-operation granularity;
this example has no wide operation. FR-30 concerns printed output; this one
survives projection to a returned integer. Narrowing the reduction claim to
main's readout would not eliminate it.

**Proposed disposition:** log a fidelity bug and add a reproducer. Refine the
scheduling boundary for this observable operation, or refuse the unsupported
concurrent shape by name pending that work. A generic statement that the
concurrency reduction is unproved does not distinguish these silently admitted
wrong results for an executable user. No fix is made in this review.

### F2 — the generated Go oracle drops imported-package initialization

Three files suffice:

```go
// main.go
package main
import ("audit/side"; "audit/state")
func Subject() int { return state.N }
func main() { _ = side.Token; println(Subject()) }

// audit/side/side.go
package side
import "audit/state"
var Token int
func init() { state.N = 7 }

// audit/state/state.go
package state
var N int
```

**Measured:** original Go exits 0 and prints `7`; GoLean `Subject` exits 0 with
`status:ok`, integer **7**. `coverageharness --subject Subject` generates a
program that exits 0 with a valid `registered\n` acknowledgement and an
`ok` observation containing integer **0**, with empty stderr. The generated
`main.go` imports only `audit/state`.

**Cause:** `tools/coverageharness/main.go:201` removes the original `main`;
`:213` calls `pruneUnusedImports`; that helper's `:397`–`:402` drops an import
whose name is no longer referenced. It also drops the imported package's
initialization, even though that initialization changes the selected subject's
result. Copying the dependency's files into the generated GOPATH does not cause
Go to initialize a package it no longer imports.

The [Go initialization rule](https://go.dev/ref/spec#Program_initialization)
does not condition an imported package's initialization on executing the
function that refers to it. Removing the original entry function is expected
here; removing its imports' initialization is not equivalent.

**Impact:** the differential runner compares the model of the original package
against an altered Go program. This witness produces a false mismatch against
a correct model result. No false PASS on an existing corpus row is claimed.
The corrupted oracle is nevertheless on the declared trust surface and could
mask a model defect with the same effect.

**Existing-record check:** prior reviews discuss removing `main` and pruning
`fmt`, and the recent intn audit discusses guessing import names. I found no
record of silently deleting a side-effecting import. This is distinct from
BUG-061's model-side static-initialization scheduling issue: GoLean is correct
on this witness.

**Proposed disposition:** preserve removed imports as blank imports, retaining
their original package dependency and initialization; test the generated oracle
against the original package on a side-effecting-import witness. An explicit
refusal is also preferable to silently changing the subject. No fix here.

### R1 — the parked `uintptr` identity defect remains live

**Not a new discovery.** It is recorded in
`docs/2026-09-05_typed-consumer-sprint-handoff.md`, decision 2, and the held
`typed-uintptr-identity` work. It is absent from the current punch list's
enumeration of silently wrong behaviors and has no active BUGS entry of its own.
The historical staged number “BUG-107” is not this defect's current number.

Six fresh probes all lower and finish with `status:ok`:

| Expression / operation | Go | GoLean |
|---|---:|---:|
| `any(uintptr(1)).(uint64)` comma-ok | false | true |
| `any(uintptr(1)) == any(uint64(1))` | false | true |
| Type switch, `case uint64: 64; case uintptr: 1` | 1 | 64 |
| `len(map[any]int{uintptr(1):7, uint64(1):9})` | 2 | 1 |
| `any([]uintptr{1}).([]uint64)` comma-ok | false | true |
| `any(&uintptrVariable).(*uint64)` comma-ok | false | true |

`NativeToIR.lean:398` maps `uintptr` to `.uint64`. This exceeds a width pin:
[numeric type identity](https://go.dev/ref/spec#Numeric_types) distinguishes
these types even when they have the same size. Refusing to *observe a uintptr
value* does not protect boolean/integer results computed using its identity.

**Proposed disposition:** restore the held decision to the release backlog,
with its actual wrong-answer scope and named owner. Respect the existing D1
hard stop; this review does not authorize landing the parked repair.

### R2 — FR-30 is a silently admitted wrong-answer class, not a named refusal

**Not a new discovery.** `docs/language-coverage-ledger.md`, FR-30, already
records that a goroutine's consecutive prints cannot be interrupted inside a
registry-free segment. The release punch list's debt table instead groups the
frontier rows as refusing by name; FR-30 explicitly does not.

Fresh reproduction: parent prints `A`, calls the same finite `delay(100)`,
prints `C`, then joins a child that prints `B` and sends on the join channel.
DFS returns exactly **`{"ACB","BAC"}`**. Pinned gc `-race`, 1,000 calls,
exits 0 with outputs **ABC 57, ACB 942, BAC 1**, no race diagnostic. This
is a useful repeatable sampling aid for the existing finding, not another
independent new scheduler bug. Dedup correctly refuses printing programs.

**Proposed disposition:** name FR-30 among the release's known silent
discrepancies; do not count it with constructs blocked by named refusals.

### F3 — dedup's accepted caps and the new CLI documentation disagree

On F1's wire, `coverage-observations --engine dedup --cap 1` exits **0**, prints
**two** observations, and reports `certified=checkCert`. DFS with `--cap 1`
exits **1**, prints no members, and names the observation-cap refusal.
Dedup also succeeds with `--fuel 0 --max-width 1 --max-sites 0 --cap 1`.
As a control, dedup with `--work-cap 1` refuses by name.

`GoLean/CLI.lean:1762` passes only `cfg.workCap` into the engine, and the
post-certificate path never checks `cfg.cap`. The resulting certified set is
not shown wrong by this finding; the issue is silently ignored API constraints.

**Overlap check:** inert dedup `width`/`sites` were already documented by
`docs/2026-09-20_unseq-stage-d-audit.md` F4 and the membership-lane design.
Do not count those again as a new discovery. However the in-flight
`docs/release-docs-1012` version of `docs/cli.md:97`–`:105` says every cap
fails loudly and describes the observation cap without the engine exception.
The reproduction extends the check to the observation cap and fuel as well.

**Proposed disposition:** correct the in-flight documentation and explicitly
scope/reject/enforce inapplicable flags. Avoid changing the mathematical meaning
of a dedup certificate merely to implement a DFS-specific budget.

### F4 — `LEAN_TRACE_TIMEOUT_SECONDS=0` or malformed text disables the alarm

`scripts/diff-coverage:109` validates the build, Go, Lean and enumerator
timeouts, but omits `LEAN_TRACE_TIMEOUT_SECONDS`. The tracer passes that value
directly to `run_with_timeout` at `:1157`. Its Perl `alarm` accepts `0` as
disabled and numerically coerces strings such as `none` or `nonsense` to 0.

**Measured using the runner's exact extracted validation loop and timeout
function:** each of `0`, `none`, `nonsense` passes validation, runs a short
Python sleeper, and returns 0 without stderr. This was a bounded function-level
probe, not a deliberately hung full differential run. The existing comment
above timeout validation already identifies this failure class for the other
knobs. No such validation exists for the tracer's added knob.

**Impact:** an invalid configuration silently disables a long-running strict
lane guard's wall limit. This does not demonstrate a wrong PASS. Add this knob
to the same positive-integer validation; no additional gate is needed.

## Reproduction

From a checkout of the reviewed commit with pinned Go on PATH and a built
`.lake/build/bin/golean` (build if necessary with `capped lake build golean`),
run the block below under `capped`. It uses a private temporary directory and
Go cache and removes them on exit. It rebuilds the Go frontend and harness;
generated wires, executables and observations are not retained. Sampling
frequencies vary; failure to sample `1` or `ABC` in one run is inconclusive.

```sh
capped -m 4G -- python3 - <<'PY'
import collections, os, pathlib, subprocess, tempfile

root = pathlib.Path.cwd()
golean = root / '.lake/build/bin/golean'
assert golean.is_file(), 'build golean first'
assert subprocess.check_output(['go', 'version'], text=True).split()[2] == 'go1.26.5'
with tempfile.TemporaryDirectory(prefix='golean-release-trust-') as tmp:
    t = pathlib.Path(tmp)
    env = dict(os.environ, GO111MODULE='off', GOFLAGS='',
               GOCACHE=str(t/'cache'), GOMAXPROCS='2',
               GODEBUG='panicnil=0', GOTRACEBACK='system')
    def run(argv, cwd=root, extra=None):
        r = subprocess.run([str(a) for a in argv], cwd=cwd,
            env=dict(env, **(extra or {})), text=True, capture_output=True, timeout=60)
        return r
    def write(path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    def show(label, r):
        print(label, 'exit', r.returncode, 'stdout=', r.stdout.strip(),
              'stderr=', r.stderr.strip())
    for name in ['nativefrontend', 'coverageharness']:
        r = run(['go', 'build', '-o', t/name, './tools/'+name])
        assert r.returncode == 0, r.stderr
    def lower(name, source):
        p = t/name
        write(p/'main.go', source)
        r = run([t/'nativefrontend', '--dir', p, '--out', p/'wire.json'])
        assert r.returncode == 0, r.stderr
        return p
    delay = '''//go:noinline
func delay(n int) int { if n == 0 { return 0 }; return n+delay(n-1) }
'''
    c = lower('chanlen', 'package main\n'+delay+'''
func Subject() int {
 c:=make(chan int,1); go func(){c<-1}()
 a:=len(c); _=delay(100); b:=len(c); <-c; return 10*a+b
}
func main() {
 counts:=[12]int{}; for i:=0;i<10000;i++ {counts[Subject()]++}
 println(counts[0],counts[1],counts[11])
}
''')
    enum = [golean, 'coverage-observations', '--input', c/'wire.json',
            '--function', 'Subject', '--max-width', '2', '--max-sites', '32',
            '--work-cap', '200000', '--expect-status', 'ok']
    show('F1 Go counts for 0,1,11', run(['go','run','-race','.'], cwd=c))
    show('F1 DFS', run(enum))
    show('F1 dedup', run(enum+['--engine','dedup']))
    show('F3 DFS cap=1', run(enum+['--cap','1']))
    show('F3 dedup cap=1', run(enum+['--engine','dedup','--cap','1']))
    show('F3 dedup zero fuel/sites', run(enum+['--engine','dedup',
         '--fuel','0','--max-width','1','--max-sites','0','--cap','1']))
    show('F3 dedup work=1 control', run(enum+['--engine','dedup','--work-cap','1']))

    p = t/'importdrop'
    write(p/'audit/state/state.go', 'package state\nvar N int\n')
    write(p/'audit/side/side.go', '''package side
import "audit/state"
var Token int
func init(){state.N=7}
''')
    p = lower('importdrop', '''package main
import ("audit/side"; "audit/state")
func Subject() int {return state.N}
func main(){_=side.Token; println(Subject())}
''')
    oracle = t/'oracle'
    r = run([t/'coverageharness','--input',p/'main.go','--out',oracle,
             '--subject','Subject','--expected-status','ok'])
    assert r.returncode == 0, r.stderr
    for name in ['oracle.crash','oracle.registered']:
        (oracle/name).write_bytes(b'')
    gopath = {'GOPATH':str(oracle/'gopath')}
    show('F2 original Go', run(['go','run','.'],cwd=p,extra=gopath))
    show('F2 generated oracle', run(['go','run','.'],cwd=oracle,extra=gopath))
    print('F2 acknowledgement:', repr((oracle/'oracle.registered').read_text()))
    show('F2 GoLean',run([golean,'native-json-run','--input',p/'wire.json',
                         '--function','Subject']))

    u = lower('uintptr', '''package main
func Assert() bool {var x any=uintptr(1); _,ok:=x.(uint64); return ok}
func Equal() bool {return any(uintptr(1))==any(uint64(1))}
func Switch() int {var x any=uintptr(1); switch x.(type){
 case uint64:return 64; case uintptr:return 1}; return 0}
func MapKey() int {return len(map[any]int{uintptr(1):7,uint64(1):9})}
func SliceAssert() bool {var x any=[]uintptr{1}; _,ok:=x.([]uint64); return ok}
func PointerAssert() bool {n:=uintptr(1); var x any=&n; _,ok:=x.(*uint64); return ok}
func main(){println(Assert(),Equal(),Switch(),MapKey(),SliceAssert(),PointerAssert())}
''')
    show('R1 Go',run(['go','run','.'],cwd=u))
    for name in ['Assert','Equal','Switch','MapKey','SliceAssert','PointerAssert']:
        show('R1 '+name,run([golean,'native-json-run','--input',u/'wire.json',
                            '--function',name]))
    p = lower('printgap', 'package main\n'+delay+'''
func Subject() int {
 done:=make(chan int); go func(){print("B");done<-1}()
 print("A");_=delay(100);print("C");<-done;return 0
}
func main(){for i:=0;i<1000;i++ {Subject();println()}}
''')
    r = run(['go','run','-race','.'],cwd=p)
    print('R2 Go exit',r.returncode,'output counts',dict(collections.Counter(r.stderr.splitlines())))
    show('R2 DFS',run([golean,'coverage-observations','--input',p/'wire.json',
         '--function','Subject','--max-width','2','--max-sites','32',
         '--work-cap','200000','--expect-status','ok']))

    s = (root/'scripts/diff-coverage').read_text()
    a = s.index('for _tvar in LAKE_BUILD_TIMEOUT_SECONDS')
    b = s.index('unset _tvar', a)+len('unset _tvar')
    x = s.index('run_with_timeout() {'); y = s.index('\n}', x)+2
    script = s[a:b]+'\n'+s[x:y]+'''
run_with_timeout "$LEAN_TRACE_TIMEOUT_SECONDS" python3 -c 'import time; time.sleep(.05); print("completed")'
'''
    knobs = dict.fromkeys(['LAKE_BUILD_TIMEOUT_SECONDS','GO_TIMEOUT_SECONDS',
                          'LEAN_TIMEOUT_SECONDS','LEAN_ENUM_TIMEOUT_SECONDS'], '1')
    for value in ['0','none','nonsense']:
        show('F4 '+value,run(['bash','-c',script],extra=dict(knobs,LEAN_TRACE_TIMEOUT_SECONDS=value)))
PY
```

## Scope, overlap and limits of this review

Read the strict/membership/confluent/racy lane dispatch and comparisons,
membership sampling and depth guard, the observation encoder/decoder and crash
evidence/split paths, the DFS/dedup entry and member paths, scheduler boundaries,
and selected frontend receiver/promotion/type paths. This was not a complete
line-by-line audit of every core or Go source file and not a full CI run.

A separate 29-function probe batch exercised direct/promoted value and pointer
receivers, interface captures and dispatch, nil receivers, method expressions,
aggregate copying, assignment evaluation, map clearing and scoped type identity.
28 matched pinned Go; the other hit the existing named refusal for successful
slice-to-array value conversion. No new method-promotion defect was established.

Checked the release punch list on `docs/release-readiness-1012` at `9b58f1d3`,
the docs lane at `3c142280`, the records lane at `3420c905`, the runtime lane's
uncommitted type-fail-open repair, and seeded-heap lane `6b0045cd`. None fixes F1
or F2. F3 specifically checks the new CLI document in the docs lane. Do not
re-report the in-flight decoder/frontend missing-type arms, BUG-090,
BUG-099, BUG-121, BUG-122, or the listed documentation repairs as new findings.

Executable probes used a private copy of the existing main-checkout GoLean
binary, plus frontend/harness binaries rebuilt from the reviewed source. No
Lean source changed and no fresh Lean build or full `scripts/ci --diff` was
run. Fresh reproduction can build GoLean first using the command above. The
findings rest on the concrete executions together with the cited source paths;
no existing baseline was changed or re-certified.

The complete reproduction block above was also extracted and run from a fresh
temporary directory/cache before recording this review. Every deterministic
result reproduced. That second sample exhibited F1's missing `1` 54 times in
10,000 calls (`0`: 9,934; `11`: 12), and R2's missing `ABC` 88 times in 1,000
calls (`ACB`: 912). The block completed with exit 0. These are measured sample
counts, not stable frequency estimates or exhaustive Go behavior sets.

No runtime fixes, gate changes, standing-rule changes, merges, pushes, or
edits to another worker's files were made. Generated outputs and probe scratch
are ephemeral; this report carries the conclusions and regeneration command.
