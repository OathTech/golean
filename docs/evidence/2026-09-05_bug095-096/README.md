# BUG-095 / BUG-096 red-first and fixed transcripts — the bug095-096 fidelity lane (2026-09-05)

[AGENT] lane `bug095-096`, worker under [USER] direction 3 (a highly
accurate Go semantics; a wrong answer outranks hygiene). Consuming
docs: `docs/BUGS.md` (BUG-095, BUG-096), `docs/language-coverage-ledger.md`
(Interface_types, Embedded_interfaces, Method_sets, Type_assertions,
Type_switches, Arithmetic_operators, Integer_operators), the baseline
header `baselines/native-full.tsv` (re-pin 2026-09-05).

## Conclusion

BUG-095's root is the FRONTEND: at interface dispatch sites
(`emitCall`'s interface-receiver arm, method value, method expression,
promotion wrapper over an embedded interface field) `emit.go` registered
the STATIC operand's interface name with the method's DECLARING
interface's method set; `noteInterface` was last-writer-wins, so
`j.foo()` (j : J, foo declared in the embedded I) rewrote `main.J`'s wire
TypeDef to `{foo}` (`embedding-satisfaction.interface-defs.txt`: main
`main.esJ ['foo']` and `main.esK ['foo']` — two levels lost; fixed
`['bar', 'foo']` / `['bar', 'baz', 'foo']`). The machine answered what
the wire declared — the CONTROL block (main's wire on the FIXED machine)
reproduces every wrong answer; the FIXED block (fixed wire, fixed
machine) matches gc on all nine subjects. Eight of nine are RED-FIRST
(`negative` is the control: own method present, embedded one missing,
which no collapse can turn wrong). The corpus program contains NO dispatch
of an embedding interface's own method through it, so its rows are not
emission-order-fragile (the slice-3 audit's finding about the slice-3
pins, relayed by the coordinator). BUG-096's root is the MACHINE:
`intShift{Left,Right}Result` formed `2^count` over `Int` before
normalizing; counts ≥ 2^32 aborted the PROCESS (`INTERNAL PANIC:
Nat.pow exponent is too big` — five of eight subjects, every one with a
count of 1<<32 or more), while counts in ~2^24–2^31 answered CORRECTLY
but materialized `2^count`, up to ~1.1 GB RSS (measured on main's binary
by the [AGENT audit, 2026-09-05]: 2^24 → 76 MB, 2^28 → 200 MB, 2^30 →
591 MB, 2^31 → 1116 MB, all correct; 2^32 = the first abort — the
earlier "≥ ~2^24 aborted" claim here was WRONG and is corrected per
audit finding R1); the fix saturates at the operand width first, which
removes the abort and the materialization alike. Both fixes leave the shift wire byte-identical
(`cmp` of the two shift wires) and the raft twin wire pin unmoved.

## gc oracle (go1.26.5 linux/amd64 = `baselines/go-oracle-pin`)

```
$ go version
go version go1.26.5 linux/amd64
```

`gc-embedding-satisfaction.txt` and `gc-shift-count-bound.txt` are the
`go run` outputs of the two corpus programs with a `main` that prints
each subject (and recovers the two panicking ones). Every FIXED row in
the machine transcripts equals the gc line for the same subject.

## Machine tier

* main: primary checkout `/home/dev/projects/golean` @ `ac45aedd`, clean;
  `scripts/capped lake build --no-build` → "All targets up-to-date", so
  its `.lake/build/bin/golean` is the main build. Main's frontend was
  built from that checkout's `tools/nativefrontend`.
* fixed: this lane's worktree at the commit carrying this README (the
  frontend from `tools/nativefrontend`, the binary from `scripts/capped
  lake build`). Lean toolchain: the repo's `lean-toolchain` pin. The
  [AGENT audit, 2026-09-05] re-certified the lane tip (93762101) on a
  CLEAN tree: full `ci --diff`, 3419/3419, `git_dirty=false`.
* audit fix round (2026-09-05, findings R1–R7 + the merge-train clause):
  records corrected here and in `docs/BUGS.md`; frontend changes (R3
  conflict rollback, R4 promoted method expression, R5 final re-check,
  R7 dedup) and the R6 docstring are gated by their own `ci --diff`
  (tail in the commit message); the born rows
  `interfaces/embedding-satisfaction/method-expr-promoted` (PASS, R4)
  and `multipkg/same-name-anon-iface` (FAIL by design, BUG-097 — the
  R2 finding) are on the baseline with a re-pin note.
* merge train round 15 (2026-09-05, [AGENT] rebase reconciliation): the
  lane (tip b283ab4c, forked from main `ac45aedd`) was rebased onto main
  `102f4dae`, which had gained flaky-panic-wait, g6-reflect-memo,
  fr27-fr28, c-arc-gu and stdlib-slice-3 at round 14. The "slice-3
  merged first" arm of the BUG-095/096 MERGE-TRAIN NOTE happened:
  slice-3's four pins of these two bugs
  (`generics/type-switch-interface-param{,/bound,/plain}`,
  `ints/shift-count-huge`) were re-pinned FAIL→PASS (stage `-`) and
  appended to this lane's FIXED entries' Cases lines; the tracked
  baseline is 3498 = 3252 PASS / 246 FAIL (main's 3479 = 3230 / 249 +
  this lane's 19 born rows + the 4 flips), re-derived from the data rows.
  The `ac45aedd` / 3419 figures above are the lane's pre-rebase record.
  Gate at the rebased tip: see the commit message's `[rebased …]` trailer
  and the ci tail reported to the merge train.
* Host: linux/amd64 (the 32-core build box; nothing here is timing-sensitive).

## Artifacts

* `embedding-satisfaction.wire-main.json` / `.wire-fixed.json` — the
  frontend wire for `Corpus/coverage/exec/interfaces/embedding-satisfaction/main.go`
  from main's and this lane's emitter.
* `embedding-satisfaction.interface-defs.txt` — the interface TypeDefs of
  both wires (the one-line diagnosis: `main.esJ` loses `bar` on main).
* `shift-count-bound.wire-main.json` / `.wire-fixed.json` — the same for
  `Corpus/coverage/exec/ints/shift-count-bound/main.go` (byte-identical).
* `bug095-machine-transcripts.tsv` — RED-FIRST (main wire, main machine),
  CONTROL (main wire, fixed machine), FIXED (fixed wire, fixed machine);
  columns subject / exit code / `native-json-run` output.
* `bug096-machine-transcripts.tsv` — RED-FIRST (main machine) and FIXED.
* `gc-embedding-satisfaction.txt`, `gc-shift-count-bound.txt` — gc output.

## Reproduction (from the repo root, this lane's tree)

```
# frontends
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go build -o .tmp/b095/nf ./tools/nativefrontend
( GO111MODULE=off GOCACHE=$OLDPWD/artifacts/go-build-cache \
    go build -o $OLDPWD/.tmp/b095/nf-main ./tools/nativefrontend )   # main @ ac45aedd
# wires (each corpus main.go copied alone into a scratch dir)
mkdir -p .tmp/b095/es .tmp/b095/sh
cp Corpus/coverage/exec/interfaces/embedding-satisfaction/main.go .tmp/b095/es/
cp Corpus/coverage/exec/ints/shift-count-bound/main.go .tmp/b095/sh/
EV=docs/evidence/2026-09-05_bug095-096
.tmp/b095/nf-main -dir .tmp/b095/es -out $EV/embedding-satisfaction.wire-main.json
.tmp/b095/nf      -dir .tmp/b095/es -out $EV/embedding-satisfaction.wire-fixed.json
.tmp/b095/nf-main -dir .tmp/b095/sh -out $EV/shift-count-bound.wire-main.json
.tmp/b095/nf      -dir .tmp/b095/sh -out $EV/shift-count-bound.wire-fixed.json
cmp $EV/shift-count-bound.wire-main.json $EV/shift-count-bound.wire-fixed.json
python3 -c 'import json
for tag in ["main","fixed"]:
    w=json.load(open(f"docs/evidence/2026-09-05_bug095-096/embedding-satisfaction.wire-{tag}.json"))
    for t in w["types"]:
        if t["def"]["kind"]=="interface": print(tag, t["name"], [m["name"] for m in t["def"]["methods"]])'
# machine transcripts: for each subject S of the row dir,
#   <bin> native-json-run --input <wire> --function S     (bin = main's or this tree's .lake/build/bin/golean)
# gc oracle: the corpus main.go with a printing main (see gc-*.txt headers)
GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go run <scratch>/main.go
# differential rows
scripts/capped scripts/coverage run --prefix interfaces/embedding-satisfaction
scripts/capped scripts/coverage run --prefix ints/shift-count-bound
```
