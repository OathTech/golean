# Lane A2 — coverage-ledger & frontier shortcut census (fidelity assessment)

[AGENT] lane worker report, 2026-08-31. Plan:
`docs/2026-08-31_fidelity-assessment-plan.md` (Lane A, coverage/frontier
half). Evidence: cited per row; probes re-run under `scripts/capped`
where noted. Nothing outside this file was modified. Sub-analyses
(BUGS.md classification; negative-corpus audit) were run by worker
agents under this lane's direction; their findings are incorporated
with the evidence they cited, spot-checked here.

Scope note: two probes could not use `/tmp` (nono sandbox: `/tmp` is
write-only here — `nono why --path /tmp/fails.txt --op read` →
`DENIED … grants write access … but read was requested`); scratch went
to an untracked in-worktree dir instead, removed at the end.

---

## 0. Summary

### 0.1 Verdict counts (census rows §5)

| verdict | rows |
| --- | --- |
| KEEP (fresh argument recorded) | 12 |
| REOPEN (work + cost) | 12 |
| ESCALATE (concrete [USER] decision) | 5 |
| **total census rows** | **29** |

Underlying populations censused: 14 live FR rows + 1 retired; 10 Q
rows; 6 T-gaps (+1 done); 28 grade-D ledger rows as a class; 5
§5.1 not-queued reasons; 69 BUGS.md entries (8 open / 61 fixed);
172 baseline non-PASS rows (all 172 mapped, see §2); 390 negative
rows as a class.

### 0.2 The 143 frontend-export refusals, by language feature

Every row maps to exactly one group; arithmetic verified mechanically
against `baselines/native-full.tsv` (143 exactly, zero unmapped, zero
double-mapped — this table supersedes the ledger §8's stale 169-red
arithmetic for the frontend-export stage).

| # | feature group | reds | recorded decision? | disposition | cost to support |
| --- | --- | --- | --- | --- | --- |
| 1 | stdlib extern surface (fmt 15, quarantine-blocked method calls 4, slices.Sort*/SortFunc 4, strconv 1, strings 1, shim-refusal-unrecoverable 3, qualified-identifier/timezone 2) | 30 | PARTIAL — FR-14 (7 reds) is queued; the other 23 are post-vintage arc-log-owned refusals with **no FR row**; ledger §8b itself says promotion is "left to the audit" | REOPEN: enumerate the shim boundary as first-class FR rows | S (enumeration) / L (support) |
| 2 | complex numbers (FR-15 + 7 satellites) | 27 | YES — queue #15, deliberately last, [USER]-directed | KEEP queue position; note it is 19% of the frontier | L (the one large arc) |
| 3 | sync design questions, frontend-export subset (Q-SYNCVAL 5, Q-COND 3, Q-ATOMIC 3, Q-SYNCLIT 2, Q-TRYLOCK 1) | 14 | YES as questions — but every owner is "W3.2" or "F4 arc", **parked** since the repo split | ESCALATE (orphaned ownership) | M–L each |
| 4 | init-order quarantine: unlowerable package-var initializers (H-11) + dispatch teeth | 11 | YES (raft W4.1/W4.2 logs) — but really the stdlib-surface boundary again (`os.Getenv` etc. poison the cell) | fold into group 1's enumeration | rides group 1 |
| 5 | range-over-func iterators, Go 1.23 (FR-12) | 9 | YES — queue #12 | KEEP queued | M–L (2–4 days est.) |
| 6 | anonymous non-empty struct TypeIds (FR-13) | 8 | YES — queue #13 | KEEP queued | M (small arc) |
| 7 | receive-in-short-circuit + BUG-032 len-hoist over-refusal (FR-2 4 + A6 4) | 8 | YES — queue #2 + mini-slice A6 | REOPEN priority (A6 also gates BUG-062) | S–M |
| 8 | tuple-component interface boxing (FR-7) | 6 | YES — queue #7 | KEEP queued | M (1–2 days) |
| 9 | `go` of a builtin callee (FR-1) | 5 | YES — queue #1, est. ½ day, **still unconsumed 12 days later** | REOPEN (queue stagnation evidence) | S |
| 10 | backward-goto fresh-cell lowering (FR-11) | 5 | YES — queue #11 | KEEP queued | M (1–2 days) |
| 11 | map-element multi-assign targets (mini-slice A3) | 5 | YES — (a)-queued | KEEP queued | S |
| 12 | assignment-form range, non-identifier targets (FR-6) | 4 | YES — queue #6 | KEEP queued | S–M (~1 day) |
| 13 | method-expr deref adapter + method stencils (FR-3 2, FR-4 1) | 3 | YES — queue #3–4 | KEEP queued | S |
| 14 | named-result shadow refusals (BUG-068 red-by-design rows) | 2 | YES — BUGS.md entry, boundary corrected at audit | KEEP | S |
| 15 | sync op in expression position (FR-5) | 1 | YES — queue #5 | KEEP queued | S |
| 16 | singletons: chan type args (A4), shadow-capture (A5), C6 local-type-arg (ratified impossibility), Q-GOEXIT marker, unsafe boundary marker | 5 | YES each | KEEP (C6/unsafe: impossibility/out-of-language, fresh args §5) | S / n-a |
| | **total** | **143** | | | |

**C1 verdict material:** the boundary is overwhelmingly deliberate —
140/143 refusals sit on a named FR/Q/A/(c)/BUGS row and every refusal
message names its cause at the failure point (verified by capped
re-runs, §2.4). The two honest exceptions: (i) 23 stdlib-shim reds are
owned by arc LOGS, not by the frontier TABLE that claims to be "one
row per unsupported feature" — an enumeration debt the ledger itself
flags; (ii) the 3 `min-max-vs-call-order` reds are on **no §8 row at
all** (reconciler C4 HIGH, §2.1).

### 0.3 The five highest-stakes rows

1. **ORPHANED ROUTING (census A2-Q1, ESCALATE)** — every
   concurrency-entangled design question (10 Q rows, 21 reds), every
   (c)-pin re-envelope obligation, and 4 open BUGS entries
   (BUG-002/004/059/065) route to "W3.2" or "the F4 arc" — reasoning-era
   arcs parked whole on `park/reasoning-2026-08-31`. Post-split, **no
   open set-aside in the coverage ledger has a live owner.** The ledger
   reads as fully-triaged while its entire triage routing dangles.
2. **BUG-062 (A2-B1, REOPEN S–M)** — the tip carries 5 differential
   reds that are SILENT WRONG ANSWERS at spec-FORCED points (len/min/max
   vs call order: machine prints 5 where gc prints 1; wrong panic
   order), the project's own worst class, owned by "mini-slice A6
   (queued)" — a queue position, not an arc, since 2026-08-19 (widened
   2026-08-22). Under "everything real Go code does" this is the top
   open fix, and it is cheap.
3. **The stdlib boundary is the real C1/C2 frontier (A2-F2, ESCALATE)**
   — 41 of 143 frontend-export reds (30 shim-surface + 11
   init-quarantine) are stdlib-surface refusals, vs 27 for complex.
   Real-world Go imports fmt/os/strings pervasively: the modeled
   fragment excludes most real programs at the import line, and the
   ledger's frontier table under-represents this (FR-14 counts 7 of the
   41). The queue ordering (complex = the one large arc; stdlib = row
   14) was set under the raft plan; under the new "lower bound =
   everything real Go code does" goal the priorities plausibly invert.
   Needs a [USER] call, not a lane worker's.
4. **The negative lane's header claims a check that does not exist
   (A2-N1, REOPEN S)** — `baselines/negative-full.tsv:2` says `oracle:
   go build (rejection) + frontend fail-closed`; the runner
   (`scripts/coverage-negative:101-111`) runs `go build` only — no
   GoLean tool ever sees the 390 negative programs. Grade-D static
   semantics rests on gc-only, substring-level rejection pinning, with
   the embedded-go/types-vs-PATH-toolchain skew unchecked. Fail-open
   flavored overstatement in a trust-adjacent header.
5. **The coverage claim's own closing invariant is false at tip (A2-L7,
   REOPEN S)** — ledger §8 asserts "169 reds, every one on a named row,
   zero unmapped" over a baseline of 172; `tools/reconcile-records`
   reports it as two standing HIGH findings ([01], [02]) and has since
   2026-08-22. The mechanism §8 promised ("the next drift surfaces in
   seconds") exists but is not a gate (exit 0), so the drift surfaced
   and then stood for 9 days.

---

## 1. The ledger's non-clean states (docs/language-coverage-ledger.md)

### 1.1 Frontier rows FR-1…FR-15

All censused in §0.2 above; per-row refusal points (file:line + error
string) are in ledger §4 and were spot-verified by re-run (§2.4).
FR-8 retired 2026-08-22 (landed; BUG-014 closed) — retirement record is
clean (§8b). FR-5 correctly re-scoped rather than retired (§8b's
honest reading). Queue consumption to date: **zero of the 14 live queue
slots consumed via the queue** (FR-8/FR-5 movement came from raft W4
arcs, not queue arcs) since the queue was established 2026-08-19.

### 1.2 T-gaps (ledger §7)

| id | gap | state under the new goal |
| --- | --- | --- |
| T-1 | literal-grid LEGAL values (Integer/Float/Rune/String literals): rejected-line covered only; legal-value pinning owed | REOPEN S — pure curation; four covered(B) rows cite it |
| T-2 | Comparison_operators: no single row-by-row suite of the operator table | REOPEN S |
| T-3 | Order_of_evaluation's own unspecified example as a membership row | blocked on the E3/E4 envelope decision — rides A2-Q2 (orphaned) |
| T-4 | import forms (renamed/blank/dot): no dedicated exec suite | REOPEN S |
| T-5 | untriaged-ids disposition column | DONE 2026-08-20, verified live (`baselines/untriaged-ids`: 11 coverage / 4 latitude / 0 wrong-answer, ceilings match) |
| T-6 | mem#chan buffered-capacity clause: no dedicated litmus | REOPEN S — a memory-model normative clause with zero direct witness |
| T-7 | mem#badsync's three exhibits as verbatim racy-red ports | REOPEN S |

None of T-1/2/4/6/7 has an owner-with-a-date; all are "curation
mini-slice" homes with no mini-slice scheduled. Cheap, and exactly the
kind of depth "incredibly well validated" buys.

### 1.3 Grade-D delegation as a class (28 rows)

**What the delegation actually supports** (fresh statement, replacing
any looser reading):

1. *Dynamic semantics of the gc-typed fragment*: both the oracle and
   the machine consume the same go/parser+go/types-checked program, so
   for ACCEPTED programs a static-semantics divergence between the two
   sides is structurally impossible. This is the strong, honest core.
2. *Static semantics by regression-pinned proxy*: the 390-row negative
   lane pins that the PATH `go build` at the ci-enforced pin rejects
   390 sampled illegal programs with stderr containing a per-case
   substring. It is a claim about **gc at go1.26.5**, in the rejection
   direction only, at substring strength (§4).
3. What it does NOT support: any model of the spec's static semantics
   (there is no Lean-side typing judgment); any bound on gc's
   conformance TO the spec (gc-laxness is structurally invisible to a
   rejection lane — L-001, the 3.5-years-unenforced `close`
   restriction, was found by spec mining, not by this lane); the C3
   direction "permitted ⊆ modeled" at the static boundary (wherever gc
   is stricter than the spec, spec-legal programs are outside the
   model; L-010 is the only annotated instance of the spec's 11
   "Implementation restriction" paragraphs).

**Grade: honest as scoped** — the D definition (ledger §1) states the
delegation explicitly and the S3 D-caveat ("constant greens attest
go/constant delegation, not GoCore arithmetic") is carried on 5 rows.
It is the right TCB choice for the goal PROVIDED the repo's coverage
claim always says "dynamic semantics of the gc-typed fragment; static
semantics delegated to the pinned frontend" — the ledger does; the
negative baseline header does not (A2-N1). The D-caveat gains teeth
when FR-15 lands: complex constant arithmetic will be the first large
GoCore-arithmetic surface where delegation stops covering for us.

### 1.4 Ledger record defects found

- **§8 arithmetic stale** (A2-L7, above): 169 vs 172; the 3 unmapped
  reds are `builtins/min-max-vs-call-order/{max-value,min-value,
  min-arg-panic}` (BUG-062 widened, launch-audit fix round, baseline
  re-pin `1730567a`). They ARE recorded (baseline header + BUG-062
  Cases) — accounting staleness, not a hidden red — but §8's "zero
  unmapped" is false as written, and reconcile-records C4 has flagged
  it HIGH since. Fix is S (re-derive §8 at tip; add min-max to the
  BUG-062/A6 bucket).
- **"marker reds" plural is wrong** (ledger §2 Package_unsafe row):
  `unsafe/boundary/sizeof-const` is PASS by measurement (constant
  folded by go/constant before unsafe is consulted — the case file's
  own header documents this precisely); only `pointer-roundtrip` is the
  red marker. S nit; the case file is more honest than the ledger row.
- **Reconciler C13 (MEDIUM)**: 66 doc sites in 4 files cite off-pin Go
  patch versions; mostly historical, worth one sweep.

---

## 2. The failing set (baselines/native-full.tsv — 172 non-PASS)

### 2.1 Stage arithmetic

143 frontend-export + 17 lean-observation + 9 differential + 1
membership + 1 nondet + 1 confluent = 172 (verified). Set-diff vs the
ledger-vintage baseline (`56a12142`): +3 (the min-max rows), −0.

### 2.2 The 143 frontend-export — see §0.2. Per-group answers to
"recorded decision or accident":

Every group traces to a recorded decision EXCEPT the enumeration
status of group 1's 23 arc-log-owned rows (recorded individually in
`docs/raft-w4-log.md`/`raft-w42-log.md`/`raft-w43-log.md` and BUGS
entries, but absent from the frontier table that claims to enumerate
"one row per unsupported feature") — a recorded-but-not-enumerated
middle state. No refusal examined was an accident: five sampled
re-runs (§2.4) all produced cause-naming refusal strings.

### 2.3 The 17 lean-observation + 9 differential + 3 singletons

lean-observation (machine-level refusal/stuck, observed at the Lean
stage — all fail-closed, none wrong answers):
- 5 `pointers/nil-array-ptr-slice*` — BUG-066's honest-STUCK sibling
  class (unmodeled slice-base nil arm), pinned per-variant by design.
- 4 abort-rendering rows (`panic-defined-payload-methods/{error,
  stringer}`, `repanic-same-value-abort` = (c)-pin C4; +
  `panic-newline-abort` = mini-slice A7 after the [USER] C4 split) —
  message-channel, not semantics; BUT the machine currently produces
  NO conforming member (BUG-004 flag, §3).
- 2 `floats/to-int-out-of-range/{nan,range}` — (c)-pin C5 / L:R6:
  refused latitude (spec: implementation-dependent). KEEP.
- Q-row members: `select-select/core` (Q-SELSEL),
  `spawn-in-init` (Q-INITSPAWN), `race/free/array-read-write`
  (Q-RACEPATH/BUG-041), `atomic-frontier/value` (Q-ATOMIC) — all ride
  the orphaned-routing escalation.
- `imported-named-key-unhashable` (FR-9/BUG-008 — stale entry, §3),
  `slice-to-array/ok-forms` (FR-10, queued).

differential (machine RAN and diverged — the only stage where wrong
answers can live):
- 5 = BUG-062 (len-vs-call 2, min-max 3): **open silent wrong
  answers**, by-design-red pending A6. Highest-stakes row 2.
- 3 = ratified (c)-pins: `init/hidden-dep-order` (C1 — spec:
  unspecified order; go/types' conforming order ≠ gc's),
  `init-order-staticinit/seq` (C2/L-011 — but see BUG-061's 1-of-11
  caveat, §3), `same-name-identity-panic` (C3 — panic-message
  rendering, impossibility argued).
- 1 = `zero-size-address/escaped-same` (L:R15 — machine holds the
  conforming never-same singleton; gc probed non-single-valued;
  version-tracked; re-envelope obligation routes to parked W3.2 →
  rides A2-Q1).
- membership `atomic-frontier/mp-litmus` (Q-ATOMIC), nondet
  `select-select/beside-loop` (Q-SELSEL), confluent
  `goroutines/worker-pool/sum` (BUG-065 — envelope uncertifiable, fix
  lane parked; §3).

The untriaged ratchet is healthy: `baselines/untriaged-ids` = 11
coverage / 4 latitude / **0 wrong-answer**, ceilings match, and the
BUG-062 rows are correctly outside it (explained by an entry). The
honest headline is still: **5 known wrong-answer rows at tip, all one
bug, fix queued nowhere active.**

### 2.4 Refusal-message probe (capped re-run, this session)

`scripts/capped scripts/diff-one` on 5 sampled reds; all refusals name
their cause at the point of failure (fail-closed doctrine holds):
- `channels/recv-order/dead-recv-len-embedded` + `bools/short-circuit-
  funclit/e6-recv-len-in-sc`: "len of a potentially-panicking operand
  in a receive-bearing function (hoisting would reorder its panic —
  BUG-032)" — confirms the A6 four are the BUG-032 over-refusal class,
  not an undocumented accident (they are absent from ledger §4 by
  design: (a)-queued, triage §3.2).
- `init/quarantined-var/read`: "references quarantined package-level
  variable … (package \"os\" surface not modeled) — the cell is
  zero-seeded but poisoned, every reference fails closed (H-11)".
- `fmt/formatter-precedence/at-depth`: "fmt.Formatter … consulted ahead
  of error/Stringer … outside the modeled subset (fail closed)".
- `strings/split-conformance/empty-sep`: shim RUNTIME refusal,
  "Unrecoverable BY DESIGN (audit R4-C-3)".

---

## 3. BUGS.md (69 entries)

Classification (sub-analysis, full 69-row table retained in the lane
transcript; spot-checked): **8 OPEN-FIDELITY-DEBT** (BUG-002, 004,
008, 041, 059, 061, 062, 065 — matches the file's own open set
exactly), **61 FIXED-HISTORICAL**, 0 primarily-latitude entries
(latitude appears as sub-records). Fixed entries cite date + arc +
case flips as the norm; `check-bugs.sh` mechanizes the Cases
cross-check; weakest citation is BUG-013 ("the fix commit", no SHA).

**10 entries flagged stale / too comfortable under the new goal:**

| BUG | flag |
| --- | --- |
| BUG-002 | its own trigger ("live the day concurrency lands") has arguably tripped — goroutine machinery landed; residual granularity re-audit routed to parked F4. ORPHANED |
| BUG-004 | abort-text quotient defensible, but the machine has NO conforming member and production is "the W3.2 lane's" — parked. 4 reds, no owner. ORPHANED |
| BUG-005 | fixed, but residual E9 cross-goroutine delete-prune widening is consume-on-demand debt inside a "fixed" entry |
| BUG-008 | STALE: promises closure by the same sub-slice that closed BUG-009 — which landed 2026-08-05; nobody re-checked in ~4 weeks. `m[sort.IntSlice{…}]` (ordinary Go) still refuses |
| BUG-032 | "fixed" but documents a LIVE broad over-refusal (any `len(f())`-shaped operand in a receive-bearing function; whole-package kill for methods) relieved only by unscheduled A6; plus two spec-unordered axes held as unreified single points consuming no Choices — exactly the settled set-aside class the mandate targets |
| BUG-041 | fail-closed but ownerless, and its over-refusal envelope is recorded as GROWING |
| BUG-059 | wrong-bytes divergence on a supported channel (import path vs package name in panics), routed to parked W3.2. ORPHANED |
| BUG-061 | **latitude framing over-reaches**: 1 of 11 residual flavors (`callinit`) is genuine optimizer latitude; the other 10 are stated chaseable, yet the whole area sits under L-011's latitude label with no owner — and the differential harness is structurally blind to it (found by construction, not corpus). Real-Go init order got deterministically wrong on 10 chaseable flavors |
| BUG-062 | the open silent-wrong-answer class; see highest-stakes row 2 |
| BUG-065 | one corpus row's concurrency envelope uncertifiable; the named fix (reduction/DPOR lane) is parked; post-split ownership of the enumeration apparatus itself is unstated. ORPHANED |

---

## 4. The negative corpus (Corpus/coverage/negative/, 390 rows)

Sub-analysis findings, spot-checked against
`scripts/coverage-negative` and `baselines/negative-full.tsv`:

- **What runs**: per case, ONE `go build`; PASS = build fails AND
  stderr contains the per-case `expected_substring`
  (`scripts/coverage-negative:101-111`). **No GoLean tool participates
  and never has** (checked to the lane's first commit). Baseline pins
  result/id/stage only; "detail omitted (churns)".
- **What the 390 rows support**: "gc at the pinned toolchain rejects
  these 390 programs with these substrings" — a regression pin on the
  delegated boundary, rejection direction only. They do NOT
  demonstrate the frontend's own fail-closed boundary (true by
  construction — `tools/nativefrontend/load.go:647` refuses on
  type-check error — but design-argument, not harness-attested), and
  they cannot see gc-laxness (a case exists only if `go build` fails;
  L-001 is the proof this direction has real findings).
- **Weak tail**: substring lengths 7–71, median 21; ~30 single-word
  substrings (`overflows`, `truncated`, `redeclared`, …) would survive
  a reword or even a different-reason rejection.
- **Skew gap**: the frontend's EMBEDDED go/types is whatever toolchain
  built the tool; the lane tests PATH `go build`; nothing detects a
  skew between the two. `negative-latest.tsv` carries no toolchain/
  commit meta (the exec lane's attributability fix was never ported).
- **The one dishonesty**: the baseline header's "+ frontend
  fail-closed" clause (carried since 2026-07-21) names a stage that
  does not exist. Fix S.
- Strengtheners costed: header fix (S); frontend cross-run stage over
  all 390 (S/M — turns claim (b) into a harness property AND detects
  toolchain skew); record meta + full stderr detail (S); lengthen the
  weak-substring tail (S); second frontend, gccgo/tinygo rejection
  cross-check (M); systematic gc-laxness hunting per spec
  "must"-clause (L — the divergence ledger declares the doctrine;
  nothing executes it).

---

## 5. The census rows

Format: ID | WHAT | WHERE | ORIGINAL justification | FRESH
re-derivation | VERDICT | claims.

| ID | WHAT | WHERE | ORIGINAL | FRESH re-derivation under the new goal | VERDICT | claims |
| --- | --- | --- | --- | --- | --- | --- |
| A2-F1 | 14 live frontier rows, 81+ reds, visible-red discipline | ledger §4; baseline | frontier = enumerated red, never grey; queue ordered 2026-08-19 by [USER] direction | the enumeration discipline is genuinely strong (refusals name causes; §8b retirements honest); but the QUEUE has consumed zero slots via the queue in 12 days, and its ordering encodes the raft plan, not the new goal | REOPEN — re-ratify queue order under the semantics-only charter; cost S (a decision) | C1 |
| A2-F2 | the stdlib boundary: 41/143 reds (30 shim + 11 init-quarantine), 23 with no FR row | §0.2 group 1/4; ledger §8b "left to the audit"; raft W4 logs | shim boundary rows are arc guardrails, "where the record lives" | the largest single frontier by red count and by real-world-Go weight; lower bound "everything real Go code does" fails at the import line for most real programs; frontier table under-counts it 7 vs 41 | ESCALATE — [USER]: is stdlib surface the next major arc (inverting complex-last)? plus REOPEN S: promote the 23 to FR rows | C1, C2 |
| A2-F3 | FR-15 complex, 27 reds, queued last | ledger §4/§5 | [USER] direction: one large arc, last; zero complex in raft | still coherent: zero complex in most real code; but it is 2 of 158 sections' PRIMARY frontier status and 19% of refusals | KEEP (fresh: prevalence argument survives the goal change; revisit only if corpus-representativity work says otherwise) | C1 |
| A2-F4 | small sequential FRs 1–7, 9–13 (queued, S–M each) | ledger §4/§5 | sequential default = SUPPORT | all still correct calls; ~35 reds retire for ~2 weeks of small arcs; FR-1 alone is ½ day for 5 reds | KEEP queued; REOPEN the scheduling (no arc active) | C1 |
| A2-F5 | C6: function-local defined types as type args — NOT queued | ledger §5.1(1) | gc's observable name embeds a compiler-internal counter; not a function of the language; impossibility | argument re-derived and survives: no injective spec-derived name exists; refusing is the only honest member | KEEP (fresh argument: impossibility is about gc's OBSERVABLE, not our modeling budget) | C1, C3 |
| A2-F6 | `unsafe`, `print/println`, body-less funcs — out-of-language | ledger §5.1(2,3,5), §2 rows | spec's own guards; assembly linkage unrepresentable | survive: the spec itself scopes these out; boundary visibly red (pointer-roundtrip marker) | KEEP; S nit: fix "marker reds" plural (sizeof-const is green by measurement) | C1, C3 |
| A2-F7 | BUG-068 red-by-design refusal rows (2) | baseline; BUGS.md BUG-068 | boundary drawn at audit | correct fail-closed residue of a real fix | KEEP | C1 |
| A2-Q1 | ALL 10 Q rows (21 reds) + every "routes to W3.2/F4" obligation: owners parked | ledger §6; `park/reasoning-2026-08-31`; split plan | each question has an owner arc | the owners no longer exist as live lanes; the ledger's fully-triaged appearance rests on dangling routes; concurrency latitude (atomics, select-select, Cond, Goexit, init-spawn) is frozen with no path to resolution | ESCALATE — [USER]: re-home the design questions in the semantics repo's own roadmap (they are semantics questions, not reasoning questions) or explicitly park them with a date | C1, C3 |
| A2-Q2 | E3/E4 inter-target order: PINNED known-≠-gc, envelope OPEN | ledger §2 Assignment_statements/Order_of_evaluation; BUG-032/052 records | pinned to our point, enumeration owed at A3's fix | a machine that deterministically realizes a NON-gc point of an unreified latitude, consuming no Choices, sits in tension with "no semantic choice hides in evaluator recursion" — the doctrine's own words; T-3's membership row is blocked on this | REOPEN M — reify or envelope; the most doctrine-material open latitude | C3 |
| A2-Q3 | mem#model DRF-SC fragment + racy-refusal doctrine | ledger §3 | mem#restrictions expressly permits report-and-exit | survives as doctrine; but its soundness leg (detector completeness for accepted programs) is lane-C/D territory; BUG-041's over-refusal is the recorded direction (safe) | KEEP here (fresh: refusal direction verified fail-closed; completeness question explicitly handed to lanes C/D) | C3 |
| A2-B1 | BUG-062: 5 silent wrong answers at forced points | BUGS.md; baseline differential rows | mini-slice A6, queued | the only open forced-point divergence; wrong VALUES from `min`/`max` and wrong panic order — real-Go behavior modeled wrongly today; queue position ≠ owner | REOPEN S–M, top priority | C2 |
| A2-B2 | BUG-061: init-order divergence, 10/11 flavors chaseable but latitude-labeled | BUGS.md; L-011; ledger §2 Package_initialization | staticinit pruning = optimizer latitude (C2 ratified) | ratification covered `callinit` (1/11); the other 10 are deterministic real-gc behaviors we get wrong, and the differential is structurally blind (found by construction); latitude label over-covers | REOPEN M — split the flavors; re-scope L-011 to the genuine latitude core | C2, C3, C4 |
| A2-B3 | BUG-008/FR-9: imported named types' comparability, stale closure promise | BUGS.md; ledger §4 FR-9 | "fixed for good by the same owed sub-slice" as BUG-009 | BUG-009's D5 fix landed 2026-08-05; nobody re-checked whether the D5 TypeDef now answers comparability; ordinary Go still refused | REOPEN S — re-check first; possibly a near-free retirement | C1, C2 |
| A2-B4 | BUG-002 granularity + BUG-004 abort text + BUG-059 panic qualifier + BUG-065 envelope certification | BUGS.md | routed to F4/W3.2 lanes | all four orphaned by the split (see A2-Q1); BUG-002's own trigger condition has arguably fired | ESCALATE (rides A2-Q1's re-homing decision) + per-bug REOPEN after | C2, C3, C4 |
| A2-B5 | BUG-032's live over-refusal breadth | BUGS.md; the A6 four (probe §2.4) | fail-closed, relief queued A6 | over-refusal is honest but broad (whole-package kill for methods in receive-bearing functions); shares A6 with BUG-062 → one arc retires both | REOPEN S–M (same arc as A2-B1) | C1, C2 |
| A2-B6 | remaining 61 fixed entries | BUGS.md | fixed with cited flips | spot-checks pass; check-bugs mechanizes Cases; two residuals inside "fixed" entries flagged (BUG-005 E9 widening, BUG-014 chan-on-nil untested corner) | KEEP (fresh: the mechanical Cases check is the argument, not the prose) | C4 |
| A2-L1 | grade-D delegation (28 rows) as a class | ledger §1/§2; §1.3 above | delegation = structural impossibility of divergence on accepted programs | survives, restated precisely (§1.3): dynamic semantics of the gc-typed fragment + rejection-pinned proxy; NOT a static model, NOT a bound on gc-vs-spec | KEEP with the §1.3 restatement as the citable claim | C1, C3, C4 |
| A2-L2 | S3 D-caveat: constant greens attest go/constant, not GoCore arithmetic | ledger §2 (Constants, Representability, Constant_expressions, Iota) | caveat named at S3 audit | honest and currently benign (constants are compile-time); becomes load-bearing at FR-15 (first big GoCore-arithmetic surface) | KEEP; note the FR-15 coupling in the arc charter when it runs | C2, C4 |
| A2-L3 | R14/U-3: constant precision extremes delegated-unknown | ledger §2 Constants; latitude inventory | recorded unknown | still an unknown with no probe; spec mandates minimum precisions — a targeted probe grid is cheap | REOPEN S (probe grid at the spec's minimum-precision bounds) | C3 |
| A2-L4 | T-1/T-2/T-4/T-6/T-7 curation gaps | ledger §7 | recorded-not-built, judgment logged | all five survive as real gaps; zero owners; T-6 is a normative memory-model clause with no direct witness — the least defensible to leave | REOPEN S each (one curation mini-slice sweeps all five) | C2, C4 |
| A2-L5 | T-3 membership row for the spec's own unspecified example | ledger §7 | blocked on E3/E4 envelope | genuinely blocked; rides A2-Q2 | KEEP (blocked, correctly) | C3 |
| A2-L6 | §8 closing arithmetic stale (169 vs 172) | ledger §8; reconciler [01][02] HIGH | "re-derived mechanically… zero unmapped" | false at tip; the reconciler catches it but is not a gate, and the finding stood 9 days | REOPEN S — re-derive §8; [USER]-question: should reconcile C4 be gate-strict? | C1, C4 |
| A2-L7 | reconciler C13: 66 off-pin version cites | reconciler output | — | mostly historical docs; one sweep distinguishes historical from claim-bearing | REOPEN S | C4 |
| A2-N1 | negative baseline header claims nonexistent frontend stage | `baselines/negative-full.tsv:2`; `scripts/coverage-negative` | header carried since 2026-07-21 | "+ frontend fail-closed" names no stage that runs; overstatement in a trust-adjacent header | REOPEN S — fix header, or better: add the 390-case frontend cross-run and make it true | C4 |
| A2-N2 | negative lane: gc-only, substring-level, no meta | §4 above | rejection pinning is the lane's job | claim honest as scoped (§1.3); weak substring tail + missing meta + embedded-toolchain skew are cheap hardening | REOPEN S/M (frontend cross-run S/M; meta S; substring tail S) | C4 |
| A2-N3 | gc-laxness direction structurally invisible | §4; L-001 precedent | divergence ledger declares the hunting doctrine | nothing executes it; a "must"-clause → rejection-witness crosswalk is the systematic form | REOPEN L (or hand to lane C as census-completeness work) | C3, C4 |
| A2-N4 | L-010: gc-strictness annotations exist on 1 of 11 implementation-restriction paragraphs | `docs/spec-divergence-ledger.md:189` | audit-added note on one case | the other 10 paragraphs unswept; each unannotated pin silently equates gc-realization with spec-force | REOPEN S–M (annotation sweep) | C3 |
| A2-U1 | untriaged ratchet: 11 coverage / 4 latitude / 0 wrong-answer | `baselines/untriaged-ids`, `untriaged-count` | T-5 disposition split | verified live and matching; the 0 wrong-answer floor is real and the 15 ids re-derive | KEEP (fresh: re-verified at tip this session) | C4 |
| A2-U2 | goose-parity red `goroutines/worker-pool/sum` (confluent) | baseline; `docs/goose-parity-parked.md` (parked branch) | BUG-065's narrowed row | the owning doc itself lives on the parked branch — a semantics-repo baseline red whose primary record is not in this repo | ESCALATE (rides A2-Q1; also: copy the owning record into this repo's docs) | C4 |

---

## 6. Unanticipated findings (beyond the brief's populations)

1. **The parked branch holds records for live baseline reds** (A2-U2):
   `goroutines/worker-pool/sum` is red in THIS repo's baseline while
   its owning record (`docs/goose-parity-parked.md`) lives on
   `park/reasoning-2026-08-31`. The split moved provenance off-repo
   for at least one tracked red.
2. **Snapshot refs are provenance-load-bearing**: ledger §4's refusal
   points cite triage commit `0c21aa21`, resolvable ONLY via
   `refs/snapshots/bugfix-arc-prerebase` (ledger's own D7 MEDIUM-5
   note). A worktree/clone without the snapshot refs cannot re-derive
   ~15 refusal-point citations. Worth a lane-D look at whether the
   fidelity-assessment's "hostile outsider" could reproduce them.
3. **A6 is the highest-leverage single mini-slice**: it retires the
   only open wrong answers (BUG-062, 5 reds) AND the BUG-032
   over-refusal four AND unblocks T-3's membership row — 9+ rows and
   the worst-class debt for one small arc.
4. **The reconciler exists but cannot enforce**: exit 0 by design
   ("dossier material, not a build failure"); both of its HIGH findings
   at tip are real and stood since 2026-08-22. Whether C4 should be
   `--strict` in ci is a cheap [USER] decision with real drift-control
   value.
