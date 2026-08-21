# Raft W4.3 campaign log — the corpus train (W4.3 + W4.4 + owed rows + membership greens)

Lane: `raft-w43` (worktree `.claude/worktrees/raft-w43`), branch `raft-w43`
off `main` @ `521f5b57` (the W4.2 tip). Charter (the ratified launch plan,
lane A): the rendered-tier surface (the 9 named refusal causes,
guardrails-first per cause), conf-change support in the replay env, the
FULL trace differential as the milestone, the W4.2 owed-rows wave, and the
w32 charter §S3(b) membership-green conversions (case-level). Sole owner
of `tools/nativefrontend`, `Corpus/`, `baselines/`, `raftsubject/`,
`tools/raftsubject/`, `raftharness/`.

Read-first companions: `docs/raft-w42-log.md` (item 4 — THE TIER-STRENGTH
BOUND, the refusal-cause census, the owed-rows table, H-20),
`docs/2026-08-20_machine-twin-harness-design.md` §7,
`docs/2026-08-20_w32-re-envelope-charter.md` §Rulings R-1 + slice 3(b),
`docs/raft-w41-log.md` (the fmt desugar mechanism, E5/E5-T precedents).

**THE TIER-STRENGTH BOUND, carried at the head as the charter directs:**
the ok-tier is blind to delivery-order unfaithfulness (it asserts
acceptance only) and the machine/byte tier is oracle-symmetric (the same
mirror on both sides — a mirror bug is invariant under it). The rendered
tier is the FIRST tier that can falsify the replay mirror: rendered
expectations carry message order, drop markers and per-node Ready contents
verbatim against upstream's own recorded output — the only oracle in this
instrument family external to us. Every milestone claim in this log states
that bound.

## Environment notes (2026-08-21)

- Fresh worktree; `scripts/setup-deps --from /home/dev/projects/golean`
  exit 0 (goose 3be88bb, perennial 43d4efa, raft 56e3200, iris-lean
  3877dbe, go c19862e5f8) AND the Lake packages (iris 3877dbe, batteries
  fa08db58, Qq f463249) — the script populates `proofs/.lake/packages`
  now, per its updated pins table; output checked as the charter asked.
- This lane touches runtime code (`tools/nativefrontend`) and `Corpus/`,
  so per-landing gates are `GOLEAN_MEM_MAX=24G scripts/ci --diff` (no
  hatch). Three lighter lanes run concurrently: `free -g` checked before
  every full gate (84G free at the initial run), gates staggered.
- The initial full gate (`ci --diff`, this worktree's first recorded run)
  was started before any change: `artifacts/w43/ci-initial.txt`.

## The item-1 surface, measured before any code (2026-08-21)

The 9 named refusal causes (w42 census, `docs/evidence/2026-08-21_w42-census/`)
plus the riders a source read of every renderer found — the full set the
rendered tier needs, each with its gc probe recorded
(`artifacts/w43/probe-fmt/`, run at go 1.26 toolchain in this tree):

| # | cause | sites | mechanism |
|---|---|---|---|
| 1 | `fmt.Fprint` (unformatted) | DescribeReady, majority.Describe, progress/tracker String — every subject site is a SINGLE argument of static string type | desugar: Fprint(w, s) → w.WriteString(s); multi-arg/non-string refuses |
| 2 | `fmt.Fprintf`/`Fprint` over `*bytes.Buffer` | describeMessageWithIndent, DescribeEntries | E5-T shadow model of bytes.Buffer (the Builder precedent); writer allowlist gains *bytes.Buffer |
| 3 | `%v` over `[]uint64` | DescribeConfState (4 verbs) | compile-time COMPOSITE rendering: %v/%+v over slices/structs of modeled element kinds, recursively, specialized per static type; gc-probed: `[1 2 3]`, nil and empty both `[]` |
| 4 | `%q` over `string` | StateType.MarshalJSON | matrix cell add (quoter exists; ASCII bound unchanged) |
| 5 | `%+v` over struct | logSlice.valid (entryID) | the composite mechanism of #3; `{term:3 index:9}` gc-probed; bounded to struct shapes whose fields are in the matrix, fail closed beyond |
| 6 | `strconv.FormatUint/FormatInt` | quorum Index.String, VoteResult.String | E5 shims, general base 2..36 (gc-probed incl. base 36 + illegal-base panic) |
| 7 | `strings.Split` | ConfChangesFromString | E5 shim, byte-scan (upstream's own semantics is byte Index); EMPTY separator fails closed (rune splitting — recorded bound) |
| 8 | `slices.SortFunc` | MajorityConfig.Describe (H-5/W1.2) | injected GENERIC E5 shim (insertion sort) through the ordinary stencil pipeline — no GoCore change (GoCore is not this lane's); tie order is recorded latitude (upstream: "not guaranteed to be stable"), guardrail rows tie-free + one tie-insensitive-observation row |
| 9 | `Sprintf`-spread (+ `Sprint`-spread, non-const formats) | DefaultLogger bodies; the RECORDING logger | runtime-formatter E5 shims (`SprintfDyn`/`SprintDyn`): runtime format parse over the modeled verb set, runtime kind dispatch, fail-closed panic outside; Sprint's space rule gc-probed ("space iff neither neighbor is a string") |

Riders (found by reading every renderer the 309 blocks reach; each is a
named refusal today):

- **`%t` over bool** (DescribeReady's `MustSync=%t`) — parser+matrix add.
- **width `%5d`** (MajorityConfig.Describe, the one width in the tree) —
  parser accepts digit width for `%d` only; space-pad left, sign inside
  (gc-probed `[    7]`, `[  -42]`).
- **`strings.Repeat`** (MajorityConfig.Describe) — E5 shim (negative
  count panics with upstream's message).
- **plainpb enum `String()` bodies** (MessageType/EntryType/
  ConfChangeTransition/ConfChangeType) — today fail-closed panic stubs;
  traces render `MsgApp`/`EntryNormal` etc. `derive.py` gains real
  bodies over the `_name` maps (upstream generated code is
  `proto.EnumName` over the same maps; unknown values fall back to the
  decimal string, mirroring EnumName). This REMOVES a recorded delta
  (the stubs) rather than adding one. Message-typed `String()` stubs
  (proto text format) stay panic stubs — no trace needs them
  (Describe* exists precisely to avoid proto-text detrand instability).
- **`%v` over `[]ReadState`** (DescribeReady's ReadStates line — dead in
  every supported trace but inside a function that must lower) — covered
  by the composite mechanism of #3 (struct of uint64 + []byte; `[]byte`
  fields render as decimal byte lists, gc-probed).

## Plan of record (commit-sized slices, guardrails first per slice)

1. fmt matrix smalls: %q-over-string, %t, %d width. (frontend + rows)
2. %v/%+v composites (slices, structs, recursion, Stringer elements
   consulted inside composites — gc-probed D1–D4). (frontend + rows)
3. Fprint + bytes.Buffer model + writer widening. (frontend + rows)
4. strconv.Format* + strings.Split + strings.Repeat shims. (frontend + rows)
5. slices.SortFunc generic shim. (frontend + rows)
6. dyn Sprintf/Sprint (spread + non-const formats). (frontend + rows)
7. derive.py enum String bodies + subject re-derive + census re-run.
8. Item 2: conf-change support in replayenv + tracereplay
   (propose-conf-change bodies, ApplyConfChange in the apply path).
9. Item 3: the rendered tier — the recording logger (replay-env-only),
   the handler-output mirror (withIndent, log-level, "> N handling
   Ready" wrappers, deliver-msgs describe lines + drop markers +
   ordered recipient list — retiring latent divergence #2), the full
   28-trace differential, per-family agreement report.
10. Item 4: the owed-rows wave (w42 table cross-checked; land the rest).
11. Item 5: the §S3(b) membership-green conversions (C3/C4, case-level).

Judgment calls are logged inline per item as JC-30+ (continuing W4.2's
numbering); checkpoints every ≤5 units.

## The initial gate (pre-change record)

`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `521f5b57`, unchanged tree:
**RESULT: PASS**, `baseline diff FULL (2343/2343, no regression)` —
`artifacts/w43/ci-initial.txt`. This worktree's recorded run exists; no
hatch needed anywhere in this arc.

---

## Wave 1 — the instrument first: replay env v2 + enum String bodies

Landed BEFORE the frontend slices, deliberately: the rendered tier's
go-run half (mirror output vs upstream's recorded expectations) is
frontend-independent, so it validates the MIRROR against the external
oracle before any machine work — the strongest available check on the
instrument that will then judge the frontend.

**1a. `tracereplay.py` v2 + `replayenv.go` v2** (items 2+3
infrastructure). The env now mirrors upstream `rafttest`'s OUTPUT, not
just its state transitions: per block, the same string upstream's
`Handle()` returns ("ok" iff the output buffer is empty; handler errors
appended). Pieces:

- **The recording logger (JC-30).** A mirror of `RedirectLogger`: level
  names DEBUG..NONE, the level gate, printf's trailing-newline rule,
  NONE suppressing handler writes too, `log-level`'s case-insensitive
  match (`strings.EqualFold` — the first go-side run caught my
  case-sensitive version: every `log-level none` block answered the
  error string; mirror bug, fixed). SHARED across the env's nodes like
  upstream's, and REPLAY-ENV-ONLY: the twin keeps its stateless logger —
  this env is sequential measurement tooling and makes no §6
  shared-nothing claim (the W4.2 handoff's "per-node" alternative is
  moot here; recorded as the JC).
- **Latent mirror divergences #1 and #2 RETIRED** (both recorded-not-
  fixed in W4.2; the rendered tier is exactly the "moment the subset
  grows" their records named): `splitMsgs` now carries upstream's
  `!(drop && isLocalMsg(msg))` guard verbatim, and `deliver-msgs` walks
  ONE ordered recipient list with per-recipient Drop flags in
  argument-position order.
- **Conf-change support (item 2):** `propose-conf-change` (v1= and
  transition= args, body parsed by the subject's own
  `ConfChangesFromString` — the stepLeader Unmarshal path end-to-end),
  the apply path's `ApplyConfChange` dispatch, AND the piece that made
  the traces agree: upstream's **History appender-state-machine +
  `snapOverrideStorage`** are LIVE in conf-change traces (the leader
  sends the new node a snapshot whose content is History's last, and
  the follower APPLIES a snapshot from Ready) — witnessed by the
  first run's divergences (`sent snapshot[index: 2` vs `4]`,
  `(Non-Voter)` vs `(Voter)`, a refused conf change rendering as
  `EntryNormal ""`), all of which vanished when the History mirror
  landed. `processReady` now mirrors `processAppend` exactly
  (HardState, then snapshot XOR entries — the snapshot-in-Ready STOP is
  retired with the reason above).
- Three channels scored: ok-tier, machine/byte tier, RENDERED tier
  per family (families = `tracefamilies.py`'s command-anchored map,
  imported so the two instruments cannot drift apart).

**1b. plainpb enum `String()` bodies** (`derive.py`): the four enum
types' String stubs become REAL bodies — `_name` map lookup + a decimal
fallback helper mirroring the protobuf runtime's `EnumStringOf`
(fallback unreachable for every value the name maps carry; the file
stays import-free). This REMOVES the W2 stub delta rather than adding
one; message-typed `String()` stubs stay panic stubs (proto text format
— no trace needs it, `Describe*` exists precisely to avoid its detrand
instability). `derive.py --check` clean; `sweep.py` reproduces the
post-swap census EXACTLY (24 quarantined / 5 LIVE / 46 imported stubs
(2 LIVE) / 7 residual sinks — enum String bodies were never census
entries, and the change moves nothing).

**THE GO-SIDE RESULT (the mirror vs the external oracle), whole suite:**

```
28 traces, 558 blocks; supported-prefix blocks: 354 (63.4%)
OK-TIER:       206/206 ok-expectation blocks agree
RENDERED-TIER: 148/148 rendered-expectation blocks agree byte-for-byte
  every family 100%: ready dumps 70/70, pure log lines 35/35,
  raft-state 14/14, status 10/10, raft-log 9/9, message describe 8/8,
  other/mixed 2/2
```

(artifacts/w43/rendered-go-side-{pre,post-enum,post-hist}.txt — the
three-step progression: 48/148 with the mirror alone, 129/148 with enum
Strings, 148/148 with the History mirror.) The supported prefix grew
268 → **354 of 558 blocks** (conf-change unblocked the 11
"multi-line command input" stoppers). Under `go run` the mirror now
reproduces upstream's recorded output byte-for-byte on EVERY supported
block. What this does NOT yet say: anything about the machine — the
machine tier re-runs after the item-1 frontend slices land.

Scope note: the machine tier of this instrument is exercised at wave 4;
nothing in wave 1 touches GoCore, the frontend, `Corpus/` or
`baselines/`.

Wave-1 landing gate: `GOLEAN_MEM_MAX=24G scripts/ci` (fast; no runtime
change) — **RESULT: PASS** (`artifacts/w43/ci-wave1.txt`; the baseline
step judges the initial run's recorded full differential, which no
wave-1 file affects).

---

## Wave 2 (item 1, landing A) — fmt matrix widenings

Frontend: `%q` over string kinds, `%t` over bool, `%<width>d`
(space-pad left, `%d` only — `parseFmtFormat` width digits +
`goleanShimFmt{Int,Uint}Pad`), and the **composite matrix**
(`fmtcomposite.go`): `%v`/`%+v` over slices and named structs,
RECURSIVE over the static type at emit time — generated lifted
renderers (a counted loop per slice level, per-field concatenation for
structs), leaves through the SAME scalar helpers as the flat matrix,
error/Stringer consulted per element/field (gc's printValue-at-depth,
probed D1–D4), `%+v` field names propagating to every depth, nil/empty
slices both `[]`. Fail closed beyond: maps, pointers (incl.
pointer-receiver Stringer leaves), anonymous structs, floats,
recursive types (cycle guard), width on any verb but `%d`.

**Guardrails first, witnessed red**: 18 new rows (5 in
`fmt/sprintf-verbs` — q-string, q-string-empty, t-bool, d-width,
width-outside-set; 13 in the new `fmt/v-composites` — incl. the
DescribeConfState shape verbatim, the ReadStates `[]struct{uint64,
[]byte}` shape, entryID `%+v`, Stringer elements + a panicking one,
and 2 boundary rows) — all 18 FAIL at `frontend-export` pre-fix
(recorded in the focused run before the widening).

**Post-fix focused slice**: 41/46 PASS in the two families; the 5
fails are EXACTLY the red-by-design set (verb-outside-set,
nonconst-format, width-outside-set, v-map-outside, v-ptr-field-outside).
Frontend unit tests green.

**Predicted flips for the full differential (stated before the run):**
exactly 18 NEW ids — 15 PASS + 3 FAIL/frontend-export by design
(`width-outside-set`, `v-map-outside`, `v-ptr-field-outside`); zero
movement on the 2343 pre-existing ids (the parser accepts only
previously-refused forms; the composite hook runs only after the
scalar matrix misses, where every case previously refused; refusal
DETAIL text changes are not a baseline column). Baseline re-pinned
same-commit with this reason.

**The run confirmed the prediction exactly** (artifacts/w43/
wave2-drift.txt: 18 lines, every one "NEW id"). Landing gate:
`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `929dcb6e` — **RESULT: PASS,
baseline diff FULL (2361/2361, no regression)**
(`artifacts/w43/ci-landingA.txt`).

---

## Wave 3 (item 1, landing B) — writers, shims, SortFunc

Frontend, six mechanisms:

1. **`fmt.Fprint` (unformatted)**: modeled for exactly ONE operand of
   string kind (every subject site's shape) as `w.WriteString(s)`;
   multi-operand and non-string operands refuse (2 boundary rows).
2. **`bytes.Buffer` E5-T shadow model** (`importedmodel.go`):
   write-side surface (Write/WriteString/WriteByte/String/Len/Reset),
   field types mirroring upstream EXACTLY incl. the defined `readOp` —
   found by the pointer-use guardrail: a user `&bytes.Buffer{}` is
   emitted from the REAL package's type info, so the shadow TypeDef
   must declare the same fields, and the model's def now REPLACES the
   host's D5 marker at the merge (markers refuse on default values).
   Nil-receiver `String()` = `"<nil>"` (upstream's special case,
   pinned). Writer allowlist for Fprintf/Fprint: `*strings.Builder` +
   `*bytes.Buffer`.
3. **strconv shims**: FormatUint/FormatInt (bases 2..36, upstream's
   illegal-base panic verbatim — an expected-panic row), ParseUint
   (error TEXTS verbatim incl. the quoted input; the error's dynamic
   TYPE is the recorded E5 delta; base 0 and bitSize outside 0..64
   fail closed).
4. **strings.Split** (byte scan — upstream's own semantics for every
   non-empty separator; empty-sep rune explode fails closed, its row
   RED BY DESIGN), **strings.TrimSpace** (the Fields byte-pattern
   table, both ends, one forward pass), **strings.Repeat** (upstream's
   negative-count panic verbatim, an expected-panic row).
5. **`slices.SortFunc`** (`genericshim.go`): an injected GENERIC
   insertion-sort shim stenciled at the call's element type through
   the ORDINARY mono pipeline (`registerFuncInst` — the same machinery
   user generics use); `S ~[]E` narrowed to `S == []E` (recorded).
   Tie order is recorded LATITUDE (upstream: "not guaranteed to be
   stable"); rows are tie-free except `sort-ties-projected`, whose
   observation projects the cmp key and is green under ANY conforming
   order. **The REAL `MajorityConfig.Describe` shape stays quarantined
   on a NARROWER, named cause**: its `tup` is function-LOCAL, and
   local defined types as type arguments keep the standing C6-class
   refusal (the compiler-internal `·1` suffix) — pinned red by
   `sortfunc-local-type`, recorded here as the honest residual of the
   slices.SortFunc item (`Describe` is off every trace path, so the
   milestone does not need it).
6. **`cmp.Compare`**: emit-time kind dispatch (unsigned/signed/string
   shims with explicit converts); floats excluded (the NaN arm),
   refuse.

**Guardrails first**: 38 rows across 6 new packages, ALL witnessed red
pre-fix (the focused run before any frontend edit). Post-fix: 35
PASS + 4 red-by-design exactly. Frontend unit tests green.

**Predicted flips (stated before the full run): exactly 39 NEW ids —
35 PASS + 4 FAIL by design; zero movement on the 2361 pre-existing.**
The run confirmed exactly (artifacts/w43/landingB-drift.txt: 39 lines,
all "NEW id"; the 4 FAILs are the red-by-design set). Baseline
re-pinned same-commit (2400 cases, 2249/151).

**Landing gate, honestly: the `--diff` gate at `17eb6d5e` came back
RED** (`artifacts/w43/ci-landingB.txt`) — every differential/baseline
step green (2400/2400, no regression), but the bug-index cross-check
caught `empty-sep`'s missing DISPOSITION: a runtime fidelity-stage red
(the fail-closed shim panic) must be classified in
`baselines/untriaged-ids`, and I had landed it unclassified. The gate
doing its job. Fixed in the follow-up commit (`coverage` disposition +
ceiling 11→12 with the written justification), re-run green:
`artifacts/w43/ci-landingB-rerun.txt` — RESULT: PASS. Lesson carried
forward: every red-by-design row at a FIDELITY stage ships with its
disposition in the same commit (landing C does).

---

## Wave 4 (item 1, landing C) — the dynamic fmt family (cause 9)

Frontend: `Sprintf`/`Sprint`/`Sprintln` with a SPREAD `[]any` argument
— the DefaultLogger bodies' shape and the replay env's recording
logger — desugar to runtime-formatter shims (`fmtDynShimKey` bundle):
the format string parsed at RUNTIME over the same verb set as the
static desugar (no width/flags), each verb dispatching on the
argument's DYNAMIC kind — error/Stringer first for the stringable
verbs (through the injected `goleanShimStringer` interface: every
String method becomes a reachability candidate through this edge,
priced in now that the renderers lower — the JC-16 tradeoff
re-decided for the dynamic tier, recorded as JC-31), then basic kinds
+ `[]byte` + `[]uint64`. Sprint's space rule (a space iff NEITHER
neighbor is a string) and Sprintln gc-probed. EVERYTHING ELSE PANICS
FAIL-CLOSED naming the verb — an unmodeled dynamic kind or an arity
mismatch is a visible machine stop, never a rendered guess.
Fixed-arity Sprint/Sprintln keep refusing (the JC-17 quarantine
witnesses depend on it; refusal moves in-hook, same stage).

**Guardrails first**: 9 rows in `fmt/sprintf-dyn`, all witnessed red
pre-fix — incl. `logger-shape`, the DefaultLogger/recording-logger
dispatch chain VERBATIM (interface method → variadic body →
`Sprintf(format, v...)`). Post-fix: 7 PASS + the 2 bound rows red by
design, dispositioned `coverage` same-commit (ceiling 12→14, justified
in `baselines/untriaged-count`).

**Predicted flips: exactly 9 NEW ids — 7 PASS + 2
FAIL/lean-observation by design; zero movement on the 2400
pre-existing.** Confirmed exactly (artifacts/w43/landingC-drift.txt).
Baseline re-pinned same-commit (2409 cases, 2256/153).

**Integration first light (the reason this item exists):** with
landing C built, `tracereplay.py` machine-tier smoke on
`single_node`, `campaign` and `confchange_v1_add_single`: **all three
replay BYTE-FOR-BYTE under the machine including the full rendered
output** — log lines through the dyn formatter, Ready dumps through
the composite matrix, conf-change end-to-end (the stepLeader
Unmarshal path live). The full 28-trace machine tier is wave 5.

Landing gate: `scripts/ci --diff` at `840acefd` — **RESULT: PASS**
(`artifacts/w43/ci-landingC.txt`).

---

## Wave 5a (item 4) — the owed-rows wave

The W4.2 owed-rows table (docs/raft-w42-log.md item 4), cross-checked
against what exists, row by row:

| owed row | disposition |
|---|---|
| the twin as a corpus family | **LANDED**: `multipkg/mini-raft-twin` — a SELF-CONTAINED 3-node mini-raft (`mpb`/`mnode` + a schedule-driven driver: message bag with removal-by-index, S1–S3 per step, S4 at the end). NOT the subject tree (the corpus never vendors 10k lines; the twin instrument drives the real raft) — this pins the language-shape COMPOSITION in the gated corpus. `elect-propose-commit` commits 2 commands on all 3 nodes, viol=0. Deterministic ×3 (md5-identical go runs). Building it found a mini-protocol bug worth recording: the first cut's AppResp carried no commit, so the leader's commit-update ping-ponged to the drain cap — seconds native, MINUTES under the interpreter (how the corpus run surfaced it as a timeout); the fix is the honest protocol (AppResp carries the follower's commit). |
| the perturbation schedules as corpus rows | **LANDED**: `perturb-rev` (reverse-order drain), `perturb-picks` (explicit picks, commit at quorum {1,3} while 2 lags), `starve-node` (S1–S3 hold, S4=2/3 EXPECTED — conditioned safety), `duel` (two candidates one term, S1's workout). All green strict rows. |
| the logger-teeth pair | **LANDED**: `interfaces/quarantined-dispatch-teeth` — `installed` green through a modeled impl; `uninstalled` RED BY DESIGN (dispatch through the interface to a concrete method whose body keeps a standing fmt refusal is a per-declaration-quarantined stub — the machine stops the moment the call lands; go run formats). The W4.2 probe pair's mechanism, gate-visible. |
| the choice-stream membership row | **LANDED**: `mini-raft-twin/choice-order`, lane=membership — the delivery-order draw over a fresh campaign's two vote requests via the map-iteration pick (the D-11 idiom): admitted set {21, 31}, **enumerated=2 exhibited=2**. Kept MINIMAL on purpose (the two-node kernel Campaign→pick→Step): the enumerator re-executes per stream probe, so the full-driver form exceeded its work cap honestly (recorded in the case comment); the driver-level schedules stay strict rows. |
| ok-tier trace replays as corpus rows | **DISPOSED as instrument-covered (JC-33)**: the trace differential is a standing instrument (`tracereplay.py`, all three channels) whose per-trace machine runs cost interpreter-minutes-to-hours — the same wall-time bound that keeps it out of the gate keeps it out of the corpus (a corpus row would either vendor the subject tree or time out). The instrument, not a corpus duplicate, is the record; gate inclusion re-opens if an interpreter-performance pass lands (the W4.2 open question, unchanged). |
| the D-12 refusal tripwire | **LANDED**: `init/quarantined-var-writer` — the raftsubject logger.go initializer shape VERBATIM (`&T{F: log.New(os.Stderr, ...)}`), red at frontend-export by design; a future widening that silently admitted the three-axis shape flips it PASS, which is the alarm. (The related F1-widening rows `init/quarantined-var-{impure,syscall,...}` landed in the holes arc and stand — cross-checked; this row adds the WRITER-typed instance H-20's ledger entry names.) |

Landing gate: `scripts/ci --diff` at `ce961a39` — **RESULT: PASS**
(`artifacts/w43/ci-item4.txt`).

---

## Wave 5b (item 5) — the §S3(b) membership-green conversions, case-level

The w32 charter's R-1 ruling executed AS FAR AS CASE-LEVEL WORK
REACHES, with the boundary stated honestly up front: the full
conversion of the four ratified (c) rows to text-quotiented membership
greens needs machine-side surfaces this lane does not own —
`renderPanicHead` producing OUR conforming member (C4), the
display/identity split (C3), and a MethodSetRecord for the runtime
error type (C3's kind clause) — all semantic-core, the W3.2 lane's.
What case-level work CAN deliver is §S3(b)'s first clause, and it is
delivered:

- **The forced halves are PROVED, per row, in-language** — four new
  GREEN strict rows:
  `panic-defined-payload-methods/{error,stringer}-forced-half` (the
  same payloads recovered: kind via type assertion — user types carry
  method-set records — identity via the method results and value
  round-trips), `repanic-same-value-abort/forced-half` (the repanic
  caught in an outer frame and compared `r == orig` — the very eface
  identity the collapse renders, DECIDED in-language where the abort
  line cannot), and `same-name-identity-panic/forced-half` (the failed
  assert panics and is recoverable; the KIND clause recorded as
  BLOCKED on the runtime-error MethodSetRecord — probed:
  `artifacts/w43/probe-c3`, the refusal named in the case comment,
  never silently skipped).
- **The anti-laundering branch holds**: all four original rows stay
  RED at their exact prior stages (differential ×1,
  lean-observation ×3) — nothing relaxed, no comparison weakened.
  Their red now reads, per the ratification's own words, "inclusion
  is not yet checkable": the machine has no text member for C4 (the
  refusal is the absence of a member, and under the quotient a member
  need only CONFORM — the door R-1 opens for the W3.2 lane), and C3's
  member EXISTS (`interface conversion: interface {} is red/inner.T,
  not blue/inner.T` — confirmed verbatim in this run's detail) but
  the runner's exact comparison cannot quotient it case-level.
- **Both text members RECORDED per row** in the case files (gc's
  strings and ours), so the drift-visibility half of R-1 is in place
  the day the machine member lands.
- **BUGS.md cross-refs updated** (BUG-004 and BUG-059 carry dated
  R-1-conversion-state blocks naming the green forced-half rows, the
  blockers, and the no-relaxation guarantee).

The grossmith `-panic-policy kind` mapping note (R-1's
cross-instrument clause) is not re-recorded here — the charter's
§Rulings already carries it, and the observation owed back to
grossmith is theirs to consume.

**JC-32 (item 3's checkquorum question): DEFERRED, with the reason.**
checkquorum's full replay needs `tick-election` +
`set-randomized-election-timeout`, i.e. a harness-facing PIN of the
jitter draw. Per the W4.2 handoff that pin is ENVELOPE work (a
deliberate narrowing carrying a record) belonging beside W4.5's
latitude entry for the range — landing it here as a replay convenience
would be exactly the deterministic-gc-pin scaffolding the doctrine
warns against. The milestone claim carries checkquorum's stop as a
named by-design exclusion.

---

## Wave 6 — BUG-068: the rendered tier falsifies the MACHINE

The tier-strength bound's first campaign paid off exactly as the W4.2
handoff predicted, except the mirror it falsified was on the OTHER
side. The machine tier's first full batch (25 traces) came back
23/25: `confchange_v2_add_double_{auto,implicit}` DISAGREED —
`INFO 1 switched to configuration voters=(1 2 3)&&(1) autoleave` (go)
vs the same line WITHOUT ` autoleave` (machine). Diagnosis, the three
channels: not a mirror bug (both oracles run the same driver), not
latitude (a bool at a forced point) — a MACHINE-side silent wrong
answer. Minimized in two probe steps
(`artifacts/w43/probe-autoleave`) to a 40-line reproducer: **a
function-local variable shadowing a NAMED RESULT** (upstream
`ConfChangeV2.EnterJoint`'s exact shape) aliased the result slot at
the return/frame-exit seam — the wire carries names, and the return's
write landed on the inner binding while frame exit read the outer
result local. go = 111110, machine = 111010, the difference the
shadowed closure returning false.

Fixed: `tools/nativefrontend/resultshadow.go` — emit-time renaming of
shadowing locals, keyed by go/types OBJECT identity, applied at the
four local-name emission sites; shadows arising in constructs outside
the rename set (range clauses, type-switch guards, receive bindings)
REFUSE rather than alias. Guardrails: `scoping/named-result-shadow`
(4 PASS incl. the EnterJoint shape verbatim + the deferred-write and
bare-return interplays; `range-clause` RED BY DESIGN pinning the
fail-closed guard). BUGS.md gains BUG-068. Both traces re-verified:
**2/2 byte-for-byte AGREE**. Drift = exactly 5 NEW ids; baseline
re-pinned same-commit (2427 cases, 2271/156).

Worth stating for the audit: the ok tier and the oracle-symmetric
byte tier were STRUCTURALLY blind to this bug (it sat inside a
rendered log line's conditional suffix, produced identically-typed
green `ok` blocks, and the byte tier only compares our driver against
our driver — which is how it DID catch it, go-side vs machine-side,
but only because the rendered output made the divergent bit
observable at all). One campaign, one forced-point silent wrong
answer found and fixed — the rendered tier earned its charter.
