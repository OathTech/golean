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

Landing gate: `scripts/ci --diff` at `95145bc3` — **RESULT: PASS**
(`artifacts/w43/ci-bug068.txt`).

---

## Wave 7 (item 3) — THE MILESTONE: the full trace differential

**The claim, with its bounds stated before its numbers** (the
tier-strength bound, as the charter directs): the three channels are
(1) the ok tier — command acceptance, blind to delivery order; (2)
the machine/byte tier — our driver under `go run` vs under the
machine, byte-for-byte over the FULL trace string INCLUDING every
rendered block: the right instrument for "the machine executes raft
as Go does", structurally unable to see a mirror bug; (3) the
RENDERED tier — every supported block's output vs upstream's OWN
recorded expectations, the one oracle external to us: what anchors
delivery-order faithfulness and falsifies mirrors (and, this arc,
falsified the MACHINE — BUG-068). A green suite is a claim about the
SUPPORTED SUBSET only; the unsupported-command census below is part
of the claim, not a footnote.

**The run of record**: `tools/raftsubject/tracereplay.py --fuel
40000000000` at commit `95145bc3` (frontend + golean built at that
tip; only docs commits follow it on this branch), executed
setsid-DETACHED per the W4.2 environment lesson — the first attempt
was killed at ~1 h by the session background-task lifetime, an
environment bound, never a machine stop; recorded in kind. Reports:
`artifacts/w43/trace-final-p{1,2,3}.txt`, the report texts tracked at
`docs/evidence/2026-08-21_w43-rendered-tier/`.

**THE NUMBERS** (28 traces, 558 blocks; supported prefix 354 blocks
= 63.4%, up from W4.2's 268/48.0% — conf-change unblocked the 11
"multi-line command input" stoppers):

- **OK-TIER: 206/206** ok-expectation blocks agree (was 178/178 over
  the narrower prefix; the denominator grew with conf-change).
- **RENDERED-TIER: 148/148 rendered-expectation blocks agree
  byte-for-byte with upstream's recorded output — every family
  100%**: ready dumps 70/70, pure log lines 35/35, raft-state tables
  14/14, status tables 10/10, raft-log dumps 9/9, message describe
  lines 8/8, other/mixed 2/2. (Go-side full-suite report:
  `go-side-rendered-148.txt`; the final run's per-piece reports carry
  the same per-family rows for the machine-run subsets.)
- **MACHINE TIER: 26 of the 27 replayable traces verified
  byte-for-byte AGREE at the final tip** (25/25 in piece 1 + 1/1
  replicate_pause in piece 3), full rendered output included. The
  28th, `async_storage_writes`, stops at its FIRST command (empty
  supported prefix — a coverage gap, not a missing verdict; the W4.2
  convention). **`probe_and_replicate` (74 blocks, 7 nodes) is the
  one verdict IN FLIGHT at this writing** — its detached machine run
  is past 6 interpreter-hours (the ok-tier form took ~1 h in W4.2;
  full rendering multiplies the string work), an honest WALL-TIME
  bound of the instrument family, already named in W4.2's open
  questions. Reproduce/await: `tools/raftsubject/tracereplay.py
  --fuel 40000000000 --traces probe_and_replicate`. Until that
  report exists, no 27/27 machine claim is made — the same reading
  discipline W4.2 used for the same trace.

  **At branch-complete the run is STILL IN FLIGHT**, past 7.5
  interpreter-hours (detached; it survives this session and writes
  `artifacts/w43/trace-final-p2.txt` when it lands — the go-side
  half of the suite already verified this trace's ok-tier 57/57 and
  rendered 17/17 against upstream in wave 1, and its W4.2 byte-tier
  agreement at the ok-observation size stands as the prior record).
  The wall-time growth is ATTRIBUTABLE: the rendered observation
  multiplies string work, and interpreter string concatenation is
  the known perf bound (W4.2's open question, unchanged, now with a
  sharper number to motivate it).
- **Zero machine-vs-go divergences at the final tip. One was found
  and FIXED on the way** — BUG-068 (wave 6), surfaced by exactly
  this instrument's rendered channel on the two
  `confchange_v2_add_double_*` traces, minimized, fixed, both traces
  re-verified agreeing. The milestone's honest headline is not "the
  suite was always green"; it is "the widened suite CAUGHT a silent
  forced-point wrong answer the previous tiers could not see, and is
  green after the fix".

**The unsupported-command census over the 22 partial traces**
(by-design exclusions, each with its reason in `tracereplay.py`'s
docstring): compact/send-snapshot 5 stops (the subject never
compacts; the replay env keeps no History-driven snapshot commands),
async-storage-writes add-nodes 2, tick-election 1 +
set-randomized-election-timeout 1 (jitter — JC-32's deferral),
transfer-leadership 1, forget-leader 2, report-unreachable 1,
add-nodes read-only 1, process-append/apply-thread stops inside
async traces. `propose-conf-change` — W4.2's LARGEST stopper class
(11 traces) — is GONE from the census: supported end-to-end.

**Census at this tip** (`sweep-post-widening.txt`, tracked): **0 LIVE
quarantined subject declarations out of 6 quarantined** (was 24/5
LIVE post-swap): the 6 dead are `MajorityConfig.Describe` (the
function-local-type C6-class residual, off every trace path),
`DefaultLogger.{Fatal,Fatalf}` (os.Exit — dead under the installed
logger), and the 3 `MemoryStorage` mutex method-set stubs (by
design). 3 LIVE imported stubs remain — `log.Logger.{Output,Panic,
Panicf}`, the embedded `*log.Logger` inside `DefaultLogger` — dead
DYNAMICALLY under the installed logger by the standing W4.2
dead-because-the-harness-installs argument (unchanged, both halves
still probed by the teeth pair, now ALSO gate-visible as corpus
rows).

**JC-34 (item 2's "twin vocabulary if cheap"): NOT taken, recorded.**
Adding conf-change to the TWIN's event vocabulary is not cheap (a new
event kind + apply plumbing + battery re-runs of ~1 h machine time
each) and buys nothing the milestone needs: the trace tier exercises
`ProposeConfChange`/`ApplyConfChange`/the stepLeader Unmarshal path
end-to-end under both oracles across 12 conf-change traces. The twin
vocabulary widening belongs with W4.5's envelope work if wanted.

**"Executable with confidence", stated as exactly what the evidence
carries:** the machine executes etcd-io/raft's RawNode surface over
the supported command subset of upstream's own datadriven corpus —
election, replication, commit, config changes incl. joint consensus
and auto-leave, snapshot catch-up of added nodes — byte-for-byte as
`go run` does, INCLUDING every rendered observation, and the
rendering pipeline itself reproduces upstream's recorded expectations
on every supported block. Bounded by: the supported subset (the
census above), the sequential/reliable-first envelope (the twin's
standing narrowings, W4.5's obligations unchanged), the wall-time
bound on the heaviest trace, and the tier-strength structure (the
rendered tier is what anchors delivery-order faithfulness; it is
green against upstream's recorded output on all 148 blocks).

---

## Audit fix round (2026-08-22) — four reviewers, semantic fixes first

Pre-merge adversarial audit of the branch tip `433d0ee3` (four
reviewers: R1 scoping/rename seam, R2 replay-env mirror fidelity, R3
milestone-claim strength, R4 fmt/shim envelope). This section records
each fix in landing order — guardrails witnessed red FIRST, the fix,
the flips — one semantic concern per commit, full `scripts/ci --diff`
per landing. Reviewer probes preserved under `.tmp/audit-r1`,
`.tmp/audit-r4` (scratch, untracked).

### R1-C1 — the capture seam did not follow the shadow rename

**Defect.** `emitFuncLit`'s capture-argument site emitted the captured
cell's address as `{"expr":"ref","id":v.Name()}` — the SOURCE name.
BUG-068's rename (wave 6) renames a local that shadows a named result
to `<name>$shadowN`, and `resultShadowScan` prunes nested func lits
(correctly — their frames scan separately), so the one path by which a
lit reaches an outer renamed shadow is exactly this capture seam: the
ref resolved to the RESULT slot the shadow was renamed away from. A
closure over a shadow therefore read/wrote the named result — the same
silent-wrong-answer class BUG-068 fixed, one seam over.

**Guardrails witnessed red first** (probe r1-p9b/p9c, corpus rows
`scoping/named-result-shadow/closure-{write,read}`):
- closure-write: go 101, machine-before **106** (the closure's `x += 5`
  landed on the result slot: 1+5, +100 at return).
- closure-read: go 1003, machine-before **303** (the closure returned
  the result slot's 3, not the shadow's 10).

**Fix.** One line: the capture ref emits
`e.localRename(v, v.Name())` (`tools/nativefrontend/emit.go`,
capture-args loop). The enclosing function's rename map is still in
force at that point (the lit's own scan swaps in only when its body is
emitted), so the seam now names the renamed cell. The `$cap` parameter
name keeps `v.Name()`: two same-named captured objects cannot coexist
in one lit's capture set (at any use site exactly one binding named
`n` is lexically visible, and the lit body is one lexical region).

**Flips.** Full `scripts/ci --diff`: drift = exactly the two new ids,
both `-> PASS`; zero movement on the 2427 prior ids; all other gate
steps ok. Baseline re-pinned (2429 cases, 2273/156) in this commit.

### R1-C2 — the per-iteration cell machinery did not follow the rename

**Defect.** `emitForPerIteration` (the Go 1.22 fresh-cell-per-iteration
lowering for a captured for-init variable) built its seed ref
(`{"expr":"ref","id":id.Name}`) and its per-iteration cell
declarations from the SOURCE name. The init statement itself is
emitted through the patched rename-following sites, so for a loop
variable shadowing a named result the machinery split in two: the
seed pointer took the RESULT slot's address, the fresh cells declared
under the unrenamed name, and the closures (post-C1) captured the
renamed seed — per-iteration freshness silently lost.

**Guardrail witnessed red first** (probe r1-p4, row
`scoping/named-result-shadow/loopvar-capture`): go **1003** (the
three captured cells hold 0, 1, 2 — sum 3, +1000), machine-before
**1009** (all three closures saw one shared cell's final value 3 → 9).

**Fix.** The `loopVar` carrier name and the seed ref both go through
`e.localRename(obj, id.Name)` — one binding site, so declare, deref,
carrier-update, and capture all agree (`tools/nativefrontend/emit.go`,
`emitForPerIteration`). Identity for non-shadow loops (empty rename
map), so the ordinary per-iteration corpus is untouched by
construction — confirmed by the run.

**Flips.** Full `scripts/ci --diff`: drift = exactly the one new id
`-> PASS`; zero movement on the 2429 prior ids. Baseline re-pinned
(2430 cases, 2274/156) in this commit.

### R1-C3 + R1-D1 — the type-switch guard hole, and the false refusal claims

**Defect (C3).** `resultShadowScan` walks `Defs` idents — but a
type-switch guard (`switch ok := v.(type)`) binds through go/types
**Implicits** (one object per clause), which the walk cannot see. A
guard shadowing a named result was therefore neither renamed nor
refused: `typeSwitchClauseBody` declared the clause binding under the
source name and it aliased the result slot — BUG-068's exact
mechanism, alive in a construct the fix's own docstring claimed to
refuse.

**Guardrail witnessed red first** (probe r1-p7b, row
`scoping/named-result-shadow/ts-guard`): go **true**, machine-before
**false** (`return true` inside the clause wrote the clause-scoped
`ok`; frame exit read the outer result slot's zero value).

**Fix — REFUSE, judgment logged.** Pass 2 now checks every
`TypeSwitchStmt`'s guard name against the result names and refuses
with a message naming the construct. Rename-instead-of-refuse was
considered and NOT taken: it would require the clause-binding
emission site AND the func-lit Implicits capture path to follow the
rename map — two more seams of exactly the kind C1/C2 just fixed —
for a shape no target needs. Refusal is the simplest honest boundary;
widening moves it with its own rows. The row flips
differential(wrong-value) → frontend-export(refusal), red by design.

**The false claims (C3+D1).** The wave-6 record claimed "range
clauses, type-switch guards, receive bindings REFUSE rather than
alias". Reality: type-switch guards ALIASED (above), and comma-ok
`:=` targets (map index, type assertion, channel receive) are
admissible AssignStmt-DEFINE forms — RENAMED, correctly, not refused.
Both `resultshadow.go`'s header and BUGS.md BUG-068 now state the
delivered boundary, and the three comma-ok forms are pinned GREEN
(`commaok-{map,recv,assert}`, verified passing before the docstring
was allowed to say so).

**Flips.** Full `scripts/ci --diff`: drift = exactly the four new ids
(ts-guard FAIL/frontend-export by design; three commaok PASS); zero
movement on the 2430 prior ids. Baseline re-pinned (2434 cases,
2277/157) in this commit.

### R1-F1 / R4-C-2 — unexported fields stop method consultation (render raw)

**Defect.** The composite renderer consulted error/Stringer per
element/field at every depth — including across UNEXPORTED fields. gc
renders through reflection, and a value reached via an unexported
field cannot be interfaced (CanInterface is false), so fmt skips
handleMethods for that value and its whole subtree: the field renders
RAW. The machine rendered `{E<1> E<2>}` where gc renders `{E<1> 2}` —
a silent wrong answer in ordinary Go (probe r4-p1).

**gc ground truth first** (`.tmp/fixround-probes/f1`, three forms):
`{E<1> 2}`/`{A:E<1> b:2}` (unexported Stringer field renders raw, the
exported sibling still consults), `{{3} E<4>}`/`{in:{X:3} A:E<4>}`
(an unexported STRUCT field taints its whole subtree — the exported
`X` inside renders raw), `{[5 6]}`/`{bs:[5 6]}` (unexported slice
field: elements raw).

**Guardrails witnessed red first**: `fmt/v-composites/
v-unexported-{stringer-field,subtree-taint,slice-taint}` — all three
differential-red with the machine consulting Stringer through the
unexported crossing (`{E<1> E<2>}` etc. against the gc strings above).

**Fix — RENDER RAW (the refuse fallback not needed).** `fmtRenderValue`
and `fmtSliceLift` thread a `tainted` flag; crossing a non-exported
field sets it for the subtree, and a tainted leaf bypasses the
method-consultation arm into the raw kind matrix. Raw rendering
composed cleanly — structs/slices/scalars below a taint are exactly
the already-modeled raw forms — so the instruction's fail-closed
fallback (refuse the cell) was not needed as a special case: a
tainted leaf OUTSIDE the raw matrix hits the ordinary named refusal
(the same `unsup` the untainted path uses), which IS the fail-closed
fallback, for free. Judgment logged: no new refusal class introduced.

**Flips.** The three new rows red→green in the family slice; the
existing family (incl. `plusv-stringer-field`, whose Stringer field is
EXPORTED, and the two red-by-design boundary rows) unmoved. Full
`scripts/ci --diff` + re-pin recorded below.

(R1-F1 gate: full `scripts/ci --diff` — drift exactly the three new
ids `-> PASS`, zero movement on the 2434 prior ids; baseline re-pinned
2437 cases, 2280/157, in this commit.)

### R1-F2 — fmt.Formatter precedence (never checked; silent wrong answers)

**Defect.** gc's `handleMethods` consults `fmt.Formatter` FIRST — for
every verb, ahead of error/Stringer and ahead of the kind matrix. The
frontend had no Formatter check anywhere (the survey found exactly
four `types.Implements` calls, none against Formatter): a
Formatter+Stringer type rendered through `String()`, a Formatter-only
named int rendered through the int matrix — silent wrong answers in
ordinary Go.

**gc ground truth first** (`.tmp/fixround-probes/f2{,b}`):
`FMT:v:1|FMT:s:2|FMT:d:3` (Format beats String for v/s AND beats the
kind matrix for d), `fd:d|fd:v` (Formatter-only named int), and at
composite depth `{FMT:v:1}` / `{F:FMT:v:1}` — but `{2}` below an
unexported field (the R1-F1 taint applies to Format too: gc cannot
interface the value).

**Guardrails witnessed red first**:
`fmt/formatter-precedence/{over-stringer,over-kind-matrix,at-depth}` —
machine `STR|STR`, `4|5`, `{STR}` against the gc strings above.

**Fix — REFUSE at static sites.** `refuseFormatter` (fmtdesugar.go):
`types.Implements(argTy, Formatter)` with Formatter looked up from the
TYPE-CHECKED fmt import (it cannot be synthesized structurally —
Format's parameter is the named interface `fmt.State`; a failed lookup
refuses too, fail closed). Wired ahead of everything in `fmtVerbArg`,
in the `Fprint` operand arm, and per element/field in the composite
renderer's method arm (tainted leaves exempt, matching gc). Modeling
`Format` would mean modeling `fmt.State`; nothing in scope needs it.
**The dyn shim cannot see Formatter at runtime** — recorded as a bound
at `goleanShimFmtDynVerb` (stdlibshim.go) with the exact exposure
stated; verified `deps/raft` + the subject tree declare no `Format`
methods.

**Flips.** The three rows differential(wrong value) →
frontend-export(refusal), red by design. Full `scripts/ci --diff`:
drift exactly the three new ids; zero movement on the 2437 prior ids.
Baseline re-pinned (2440 cases, 2280/160) in this commit.

### R4-C-3 — shim refusals become UNRECOVERABLE machine stops

**Defect.** Every golean-bound refusal inside an injected shim body
was an ordinary Go `panic("golean ...")` — and ordinary panics are
RECOVERABLE. Ordinary defensive idioms swallowed refusals into silent
wrong answers, in three shapes (probe r4-p2): recover around a parse
(`ParseUint("0x2a", 0, 64)` — base 0 is a recorded bound — returned
v=0 ok=false where gc says v=42 ok=true), recover around an explode
(`strings.Split(s, "")` → n=0 where gc says 3), and fmt's OWN recover
around a user `String()` (`goleanShimFmtRenderCall` re-rendered a
refusal as a plausible `%!v(PANIC=...)` string where gc renders
normally). The fail-closed doctrine's "visible red beats hidden wrong
answer" was being undone by the model's own panic machinery.

**Guardrails witnessed red first**:
`panic-recover/shim-refusal-unrecoverable/{parse,split,render}-recover`
— all three differential-red with the machine's silently-wrong values
(`v=0 ok=false`, `n=0`, `%!v(PANIC=String method: golean...)`).

**Fix.** One reserved helper, `goleanShimUnsupported(msg)`, injected
beside every shim bundle and FORCE-QUARANTINED by the emitter
(`emitFuncDecl` returns `unsup` for the name, reusing the ordinary
per-decl quarantine machinery — no new wire shape, no decoder change):
a CALL to it throws `GoError.unsupported` at the interpreter level,
which never enters the `.panicking` machinery and no `recover()` can
touch. All 15 golean-bound panic sites route through it (each followed
by a dead `panic("unreachable...")` so Go's termination analysis is
unchanged). UPSTREAM-FAITHFUL panics — strconv illegal-base, strings
negative-Repeat, the `b[7]` bounds shapes — deliberately STAY ordinary
panics: gc panics there and recover must keep catching them (the
`format-illegal-base` row pins that lane green).

**Acceptance verified, not asserted**: the three rows flip
differential(wrong value) → frontend-export with the quarantine
message THROUGH the surrounding recover()s — the r4-p2 shapes are now
visible unsupported stops. The render path's recover question is moot
by construction (a throw bypasses it), verified by `render-recover`;
the frame-placement comment in stdlibshim.go updated to say what is
still load-bearing (genuine user-method panics).

**Predicted stage flips, confirmed exactly**: the three pre-existing
rows that pinned refusal PANICS — `fmt/sprintf-dyn/{arity-mismatch,
unmodeled-kind}`, `strings/split-conformance/empty-sep` — move
FAIL/lean-observation → FAIL/frontend-export (same red, honest new
mechanism). Nothing else in the 200-case fmt/strings/strconv/
panic-recover slice moved; `fmt/sprintf-dyn/stringer-panic` (a GENUINE
user panic under fmt's recover) stays green, pinning that real panics
still recover.

(R4-C-3 gate: full `scripts/ci --diff` — the only failing steps were
the two EXPECTED drifts: the native baseline (exactly the six
predicted lines above) and the wordfreq GOLDEN pin, whose wire now
carries the quarantined `goleanShimUnsupported` decl — the diff is
exactly that appended stub. Both re-pinned deliberately in this
commit; `scripts/check-golden` green on all pins after the re-pin,
and the wordfreq proof modules (`GoLeanProofs.Examples.WordFreq`,
`Audit.WordFreq`) rebuilt green against the new term. Baseline
re-pinned 2443 cases, 2280/163.)

### R1-F3 — ParseUint's range-error VALUE (the structurally-blind guardrail)

**Defect.** Upstream `strconv.ParseUint` returns the SATURATED maximum
for the bitSize alongside `ErrRange` ("the returned value is the
maximum magnitude integer of the appropriate bitSize"); the shim
returned 0. The existing guardrail `parse-uint-errors` could not see
it — it discarded the value with `_, err :=` and compared error TEXTS
only: a structurally-blind guardrail, exactly the fail-closed-
classification class the audit dimension list names.

**gc ground truth** (`.tmp/fixround-probes/f3`): 18446744073709551615
/ 255 / 4294967295 / 18446744073709551615 for the 64/8/32/64-bit range
shapes, all with non-nil errors.

**Guardrails witnessed red first**: `parse-uint-errors` strengthened
to OBSERVE the value (the blind guardrail fixed, per the finding) and
the new `parse-uint-range-value` row across three bitSizes — machine
`0 ...`/`0 0 0 0` vs gc's saturated maxima.

**Fix.** `rangeErr` returns `max` (already in scope per-bitSize);
syntax errors keep returning 0, as upstream. Both rows green; the
strconv family (incl. the upstream-faithful `format-illegal-base`
panic row) otherwise unmoved.

**Flips.** Full `scripts/ci --diff`: baseline drift exactly the one
new id `-> PASS` (parse-uint-errors changed VALUE but was red pre-fix
only in the working tree — it entered the run already green, so no
stage move). The gate also surfaced the R4-C-3 untriaged-ledger
ratchet one landing late (check 4b reads the previous differential's
latest.tsv) — resolved in the preceding follow-through commit, its
mechanism recorded in the ledger's dated log. Baseline re-pinned
(2444 cases, 2281/163) in this commit.

### R4-M-1 — fixed-arity Sprint/Sprintln modeled; the corpus-scoped-refusal inversion, fixed and logged

**Defect (an inversion, not a wrong answer).** Fixed-arity
`fmt.Sprint(a, b, ...)` — the single most common Sprint shape a Go
programmer writes — was REFUSED, and the refusal's own comment gave
the reason: "the JC-17 retargeted quarantine witnesses depend on
fmt.Sprint refusing". That is the over-specialization class inverted:
not machinery shaped by the target, but COMMON GO turned away to keep
test fixtures stable. **The lesson, logged as the audit asked**: a
refusal must be justified by the modeled envelope, never by what the
corpus's witnesses happen to lean on; and a quarantine witness must
pick its unlowerable cause by STRUCTURAL DISTANCE from the envelope
(reflection — the deep-latitude surface the closed-world frontend
excludes by doctrine), not by "currently unmodeled" (that pick has now
rotted twice: Sprintf at W4.1, Sprint here). No eternal refusal
exists; the tracked baseline flags any future flip loudly.

**Guardrails witnessed red first**:
`fmt/sprintf-dyn/{sprint,sprintln}-fixed-arity` (probe r4-p6 shapes) —
both FAIL/frontend-export under the old refusal, gc `a=1 b=true` /
`a 1 true\n`.

**Fix.** The desugar packs the args into a `[]any` (nil pack for zero
args, exactly variadic-call semantics) and calls the SAME
differentially-pinned dyn shims the spread form uses — the space rule
and rendering are the already-validated cells. Each packed arg is
Formatter-checked (R1-F2): the pack must not smuggle a Formatter
implementor past the static refusal into the Formatter-blind shim.

**The rewire — SIX witnesses, two caught mid-slice.** The audit named
four fmt.Sprint-dependent quarantine witnesses (the JC-17 fixture +
methods/quarantine-{interface,embedded,pointer-receiver},
generics/stencil-quarantine). The slice run then caught TWO MORE the
finding missed — `methods/quarantine-sibling` (its quarantined-call
row had ALREADY flipped green mid-slice: the lost-witness class,
witnessed live) and `interfaces/quarantined-dispatch-teeth` (the W4.2
logger-teeth pair, whose uninstalled half leaned on the same refusal).
All six retargeted to `reflect.TypeOf` in this commit;
`quarantine_test.go`'s fixture and cause-assertion updated
("Sprint"→"reflect"); every one holds its exact baseline stage through
the full run.

**Flips.** Full `scripts/ci --diff`: drift = exactly the two new ids
`-> PASS`; ZERO movement on the 2444 prior ids — the six rewired
witnesses' stages unmoved is itself the no-lost-witness proof.
Baseline re-pinned (2446 cases, 2283/163) in this commit.

### R4-M-2 — the dyn kind matrix routed to the static cells' helpers

**Defect (an asymmetry, witnessed as stops in ordinary Go).** The
STATIC composite matrix renders `[]int`, `[]string` and named structs;
the same values through a `logf(format, v...)` pass-through hit the
dyn shim, whose composite surface was exactly `[]byte`/`[]uint64` —
probe r4-p6's dynInts/dynStrings/dynStruct all stopped where gc
renders `[1 2]` / `[a]` / `{3}`.

**Guardrails witnessed red first**:
`fmt/sprintf-dyn/{slice-int,slice-string,struct-bound}` — all three
FAIL/frontend-export (unsupported stops) pre-fix.

**Fix — dyn arms, not the static path, judgment logged.** The
instruction's "route through the static render path" cannot be taken
literally: that path is EMIT-TIME type recursion, unreachable from a
runtime type dispatch. What delivers the same cells is what the
existing `[]byte`/`[]uint64` arms already do — shim-source arms whose
LEAVES call the same `goleanShimFmt*` helpers as the static matrix,
so the two matrices agree by construction. `[]int` (verbs v/d) and
`[]string` (verbs v/s) added. **Named structs remain a RECORDED
bound**: a runtime type switch in a pre-typecheck injected source
cannot name user types, and enumerating the user's struct types into
generated arms is machinery nothing in scope needs — the bound is
stated at `goleanShimFmtDynVerb` and PINNED by the red-by-design
`struct-bound` row (the "surprising cell", exactly as the finding
asked).

**Flips.** slice-int/slice-string red→green (byte-agreeing with gc,
negatives and multi-word strings included); struct-bound stays red by
design. Full `scripts/ci --diff`: drift exactly the three new ids;
zero movement on the 2446 prior ids. Baseline re-pinned (2449 cases,
2285/164) in this commit.

### R4-M-3 / M-4 / M-5 + L-3 — the smalls: bounds pinned, a crash named, a boundary stated

**M-3 — the two unpinned narrowings, pinned** (probe r4-p5; gc handles
both): `slices/sortfunc-cmp/named-slice-bound` (SortFunc's `S ~[]E`
freedom narrowed to `S == []E`; gc sorts `namedIDs` to 123) and
`slices/sortfunc-cmp/float-compare-bound` (cmp.Compare's float arm
excluded — the NaN-ordering latitude; SortFunc itself admits
`[]float64`, so the refusal lands on the comparator; gc returns 2).
Both witnessed red with their already-named refusal messages —
the narrowings were honest, just gate-invisible; now they are rows.
The float/named-slice bounds are hereby LOGGED as the audit asked:
they retire only by a widening with its own rows, and the
`slices.Sort`-vs-`SortFunc` asymmetry (Sort takes named slice types
but only integer elements; SortFunc the reverse) is part of what the
rows pin.

**M-5 — the `%+`-at-end-of-format CRASH becomes the named refusal.**
Witnessed live first (`fmt/sprintf-dyn/trailing-plus`): the dyn
parser's `format[i+1:i+2]` with `i+1 == len(format)` was a Go
slice-bounds panic — `runtime error: slice bounds out of range [:4]
with length 3`, status PANIC, i.e. RECOVERABLE and mislabeled, where
gc renders `x%!(NOVERB)%!(EXTRA int=1)`. The slice is now guarded and
the arm emits the named `%+<end of format>` refusal through
`goleanShimUnsupported` (unrecoverable, R4-C-3). Stage flip
lean-observation → frontend-export, red by design (gc's NOVERB
rendering stays outside the modeled subset — bound recorded).

**L-3 — refusals at partially-modeled packages name the member and
the boundary.** `strconv.Atoi` used to refuse as "package \"strconv\"
surface not modeled" — misdescribing a partially modeled package and
naming no boundary. The allowlist-miss path now refuses in place:
"strconv.Atoi is outside the modeled subset (modeled strconv
direct-call members: FormatInt, FormatUint, ParseUint — widen with a
differential pin first)" — the member list derived from the allowlist
itself, so it cannot rot against it. Applies uniformly to the four
allowlisted packages (strings/errors/bytes/strconv); the 129-case
slice over all of them showed zero movement beyond the new rows.
Row: `strconv/format-parse/unmodeled-member`, red by design.

**M-4 — the bytes.Buffer boundary, stated exactly.** The model's
docstring said "WRITE-side surface only" — overclaiming three
write-side members (WriteRune, Truncate, Grow — probe r4-p7's exact
cells) that are declaration-only stubs like the read side. It now
names the six modeled members exactly (Write/WriteString/WriteByte/
String/Len/Reset) and why every other method staying a stub is
load-bearing for the `off == 0` argument. (The resultshadow header —
the L-2 sibling of this batch — was corrected in the R1-C3 landing.)

**Flips.** Full `scripts/ci --diff`: drift exactly the four new
red-by-design ids; zero movement on the 2449 prior ids. Baseline
re-pinned (2453 cases, 2285/168) in this commit.
