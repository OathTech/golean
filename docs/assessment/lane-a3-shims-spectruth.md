# Lane A3 — shortcut census: stdlib shims, spec-truth state, owed rulings, delegation (2026-08-31)

Status: [AGENT] assessment artifact (fidelity-assessment plan, Lane A,
boundary-policy third). Every claim below is cited to file:line at this
worktree's checkout. Verdict vocabulary per the plan §Phase 0:
KEEP (with a FRESH argument) / REOPEN (work + cost S/M/L) /
ESCALATE (a concrete [USER] decision). Claims touched: C1 feature
totality, C2 lower bound, C3 upper bound, C4 validation credibility.

## Summary table (all rows)

| ID | WHAT | VERDICT | claims |
|---|---|---|---|
| A3-S1 | Shim-injection mechanism vs the [USER] retirement ruling (fired ~20 instances ago, never revisited, note cited nowhere) | **ESCALATE** | C4 |
| A3-S2 | Per-shim validation asymmetry: one fuzz (Fields, 600k) for a ~21-function/2-type, ~3,300-line hand-written stdlib model; audits, not the differential, caught the two real shim bugs | **REOPEN (M)** | C2, C4 |
| A3-S3 | fmt.Formatter invisibility at dynamic fmt sites — a RECORDED silent-wrong-answer class, bounded only by "nothing in the subject tree implements fmt.Formatter" | **REOPEN (S)** | C2 |
| A3-S4 | Dot-import stdlib call = `stuck`, not a boundary refusal — named defect since 2026-08-15, clean fix named, not in BUGS.md | **REOPEN (S)** | C1 |
| A3-S5 | The recorded per-shim deltas (error dynamic-type names, strconv error type, %q non-ASCII, ParseUint base-0, Split empty-sep, Repeat overflow, SortFunc ties) | **KEEP** (new argument; one tripwire owed) | C2, C3 |
| A3-S6 | Allowlist growth bound: "guardrail rows + fidelity argument FIRST" per function; no retirement condition, five distinct injection mechanisms accreted | **REOPEN (M)** (fold into S1 decision) | C4 |
| A3-S7 | Fail-closed on out-of-set stdlib calls — verified in code | **KEEP** | C1 |
| A3-P1 | Brief-premise correction: P2/P3/P4 all MERGED; what is incomplete is P5 + intra-phase follow-ons | (finding, no verdict) | — |
| A3-P2 | Quote-fidelity unmechanized: covmap layer validated-but-unwired; 4 CIP drafts held since 2026-08-17; the anchor lint checks resolution only, and the P2 audit found 5 misquotes it structurally cannot see | **ESCALATE** | C3, C4 |
| A3-P3 | D-caveat + T-1: constant-heavy greens attest go/constant folding, not GoCore arithmetic; legal-line value pinning owed on the literal grids | **REOPEN (M)** | C2, C4 |
| A3-P4 | Ledger curation + upstream: 15 entries vs the P4 "≥20 or recorded reason" bar; L-007/L-008 spec-bugs UNREPORTED, L-014 gc-bug UNFILED; P5 decision point never held | **ESCALATE** | C3, C4 |
| A3-P5 | Spec evolution: re-pin MECHANICS recorded, re-pin POLICY absent (no cadence/trigger/owner for new Go versions); corpus go.mod third leg still missing; inittask-std.tsv regeneration rides the pin | **ESCALATE** | C1-C4 |
| A3-Q1 | The eight Q-rows: memos complete 2026-08-21, rulings owed; 20 reds standing, incl. one probed observed-∉-modeled class (Q-INITSPAWN) and a mem-model FORCED point unmodeled (Q-ATOMIC) | **ESCALATE** (the ruling sheet exists; it needs a sitting) | C1, C2, C3 |
| A3-Q2 | `nonterm=` under `engine=dedup` (OQ5): changes what a green row asserts; unruled = dedup rows may declare a fuel nothing checks | **ESCALATE** | C4 |
| A3-Q3 | Remaining W3.2 TODO items (trace-coverage push, slice-5 print-interleaving probe, map-pick perf) | **KEEP** (parks re-argued) | C4 |
| A3-D1 | Delegation claim shape: stated precisely in the language ledger's grade-D definition but NOT in the doctrine/charter where "GoLean models Go" is claimed | **REOPEN (S)** | C4 |
| A3-D2 | go/constant common-mode channel: frontend folds with the oracle's own engine; "differential divergence structurally impossible" on delegated rows; R14/U-3 precision extremes an admitted OPEN QUESTION | **REOPEN (M)** | C2, C4 |
| A3-D3 | Monomorphization (mono.go): a 1,063-line trusted semantic transformation, no translation validation; gcshape/dictionary-vs-stencil question | **KEEP** (new argument) + residual noted | C2, C4 |
| A3-D4 | SpecTec-Go direction: the structural answer to D1/D2/D3 residuals; currently only a memory note, no repo artifact | (routing note for phase 3) | C4 |

## The five highest-stakes rows

### A3-S1 — the shim-injection mechanism vs its own [USER] retirement ruling — ESCALATE

- **WHAT.** `docs/2026-08-16_overrides-design.md:12-15` records the
  [USER] ruling verbatim: *"fine, but the injection mechanism is a bit
  of a wart and should be retired as soon as we see another
  instance."* The named retirement trigger (`:45`): **the second shim
  instance**, in favour of a linked registry of pre-lowered Funcs
  (`:46-62`). The note's own prediction (`:41-43`): "At five it would
  be a small compiler pass nobody designed, with the injected text as
  its only specification."
- **WHERE it stands today.** `tools/nativefrontend/stdlibshim.go` +
  `fmtdesugar.go` + `fmtcomposite.go` + `genericshim.go` +
  `importedmodel.go` ≈ 3,300 lines. The injected surface: 10
  direct-call shims (strings.Fields/Join/Split/TrimSpace/Repeat,
  errors.New, bytes.Equal, strconv.FormatUint/FormatInt/ParseUint —
  `stdlibshim.go:148-157`), 6 fmt desugar surfaces over ~40 injected
  helper declarations (`:176-185`, `:206-234`), 2 package-variable
  method desugars (binary.LittleEndian.Uint64/PutUint64, `:191-198`),
  2 generic desugars (slices.SortFunc stenciled, cmp.Compare kind-
  dispatched, `:165-169`), and 2 shadow type models
  (strings.Builder, bytes.Buffer — `importedmodel.go:56-177`,
  "E5-T"). That is **five distinct injection mechanisms** and ~20
  instances past the trigger.
- **The ruling was never revisited.** `docs/2026-08-16_overrides-design.md`
  is cited by NO other file in `docs/` (grep: zero hits for
  "overrides-design", "injection mechanism", "second shim" outside
  the note itself); its git history is a single commit (`9d131a4f`).
  The W4.0/W4.1/W4.3 logs that added the instances do not mention the
  retirement trigger. Each widening did carry rows + a fidelity
  argument (the per-function rule held), but the mechanism-level
  ruling was silently outgrown.
- **ORIGINAL justification** (for injection): one legible entry; no
  GoCore/wire/decoder change; golden pins record the lowered body;
  layer-3 trust story identical under registry-vs-paste
  (`overrides-design.md:155-160`).
- **FRESH re-derivation.** The trust story genuinely is unchanged by
  paste-vs-registry (the note itself proves this), so this is not a
  soundness hole. But the note's hygiene prediction has come TRUE:
  synthetic-source injection now includes an emit-time format-string
  compiler (`fmtdesugar.go`, 975 lines), emit-time type recursion
  (`fmtcomposite.go`), a force-quarantined pseudo-declaration whose
  Go body "exists for type-checking only — it is never lowered"
  (`stdlibshim.go:1213-1227`), and a shadow-package harvest with its
  own shape assertions (`importedmodel.go:26-30`). The type-checker
  checks a program the user did not write, five ways. Under the new
  goal ("incredibly faithful, incredibly well validated") the issue
  is C4-class: an outside reviewer reading the [USER] ruling and then
  the tree concludes the project overrides its own recorded
  decisions under delivery pressure.
- **VERDICT: ESCALATE.** Concrete [USER] decision: (a) re-ratify
  injection at current scale, superseding the 2026-08-16 ruling on
  the record (with a new bound — e.g. a hard cap or a
  per-mechanism census in the shim file header), or (b) schedule the
  linked-registry retirement the ruling ordered (cost M-L: pre-lower
  once, link by FuncId, golden-pin the library set — designed in the
  note already). Either outcome must be WRITTEN; the status quo is an
  un-honored [USER] ruling.
- **Claims: C4** (and C2 indirectly via S2).

### A3-S2 — per-shim validation asymmetry — REOPEN (M)

- **WHAT.** The policy's stated validation story
  (`stdlibshim.go:17-22`, `overrides-design.md` layer 3): every
  differential row crossing a shim is an oracle test; conformance
  slices per shim; "widening the allowlist owes new guardrail corpus
  rows and a fidelity argument FIRST" (`stdlibshim.go:28`).
- **What each shim actually has.** strings.Fields: 8+ behaviour-class
  rows AND a 600,000-trial shim-vs-stdlib fuzz (0 mismatches) run
  under the real Go runtime (`g2.md:739-746`). Every later shim: a
  hand-picked row set only — counted from `Corpus/coverage/exec/*/
  */cases.tsv`: strconv/format-parse 12, fmt/sprintf-verbs 46,
  fmt/sprintf-dyn 22, binary/little-endian 8, slices/sortfunc-cmp
  14, strings/trimspace-repeat 10, split 13, join 8, bytes/equal 6,
  errors/new 10 — plus gc probes in `artifacts/w43/`. **No shim
  after Fields has a fuzz.** grep for "fuzz" in scripts/tools hits
  only the Fields record.
- **Evidence the row sets are insufficient.** The two real shim bugs
  on the record were caught by ADVERSARIAL AUDIT, not by the rows:
  R1-F3 — ParseUint returned 0 instead of the saturated max on range
  error, "a silent value divergence on the error path; the guardrail
  was structurally blind to it" (`stdlibshim.go:1028-1037`, commit
  `279164e0`); R4-M-5 — the dyn fmt trailing-"%+" slice-bounds panic
  turned an intended refusal into "a recoverable, mislabeled runtime
  error" witnessed live (`stdlibshim.go:781-797`). Also R4-C-3: the
  entire refusal family was RECOVERABLE (user `recover()` turned
  refusals into silent wrong answers) until the goleanShimUnsupported
  throw redesign (`stdlibshim.go:120-132`). Three near-misses of the
  exact class the policy exists to prevent, none surfaced by the
  conformance rows.
- **ORIGINAL justification.** Pure deterministic functions: "one row
  per behaviour class pins that class outright" (`g2.md:684-687`).
  True — IF the behaviour-class enumeration is complete, which is
  precisely what the audits showed it repeatedly was not (error-path
  values, format-string edge positions, recover interaction).
- **FRESH re-derivation.** The Fields standard (behaviour-class rows
  + a randomized differential fuzz under the real runtime) is cheap —
  the fuzz harness pattern exists — and is the only evidence class
  that probes inputs nobody enumerated. Under the new goal the per-
  shim rule should be: no shim without (i) a behaviour-class row set,
  (ii) a Fields-style randomized shim-vs-stdlib fuzz (pure functions;
  parameterized trials, tracked count + seed discipline), (iii) the
  delta list (S5) restated against the CURRENT modeled subset. fmt is
  the priority target: it is the largest complex (~1,400 lines
  fmtdesugar+fmtcomposite + the injected renderers), has runtime
  format-string parsing, and its bug history is the worst.
- **VERDICT: REOPEN, cost M** (a fuzz harness per pure shim ≈ days,
  not weeks; fmt dyn-route fuzz slightly more). **Claims: C2, C4.**

### A3-S3 — the fmt.Formatter hole: a recorded silent-wrong-answer class — REOPEN (S)

- **WHAT.** `stdlibshim.go:608-619` (RECORDED BOUND, audit R1-F2),
  verbatim: gc consults `Format` ahead of error/Stringer for every
  verb; the dyn shim cannot ask "does the dynamic type implement
  fmt.Formatter" (fmt.State unmodeled). "A dynamic value whose type
  implements BOTH Formatter and error/Stringer would render through
  Error/String here where gc calls Format — **a wrong answer this
  shim cannot detect.**" Static sites refuse Formatter implementors
  (`refuseFormatter`, fmtdesugar.go; pinned by
  `fmt/formatter-precedence` rows); the exposure is a Formatter
  implementor reaching a dyn site through `any`/variadic boxing.
- **ORIGINAL justification.** "Recorded, not closed; nothing in the
  subject tree implements fmt.Formatter" — a RAFT-SUBJECT bound.
- **FRESH re-derivation.** Under the new goal the machine is a
  general Go semantics, not a raft harness: "the subject tree doesn't
  do it" is no bound at all. This is the single known place in the
  modeled surface where the machine can return an `ok` answer that
  differs from gc's — the exact fail-open class the charter calls
  "ALWAYS a defect unless explicitly authorized." A Formatter-ONLY
  implementor falls through the type switch to the unrecoverable
  refusal (fail-closed); the wrong answer needs Formatter AND
  error/Stringer on one type — narrow, but legal, ordinary Go.
- **Candidate closures** (any restores fail-closed): (a) frontend
  scan — refuse the EXPORT of any program whose package declares or
  instantiates a type with a `Format(fmt.State, rune)` method when
  any dyn-fmt shim is injected (conservative, syntactic, cheap — the
  same class of scan injection already does); (b) inject a
  goleanShimFormatter marker interface with the Format signature
  shape-only and refuse at runtime on match (needs fmt.State
  nameable — currently not, which is why (a) is the shape).
- **VERDICT: REOPEN, cost S** (option (a) is an emit-time scan +
  guardrail rows). **Claims: C2** (a modeled-surface wrong-answer
  channel), C4.

### A3-Q1 — the eight Q-rows: complete memos, absent rulings — ESCALATE

- **WHAT.** `docs/2026-08-21_w32-qrow-memos.md` — eight decision-ready
  memos with a one-page ruling sheet (`:829-849`), written 2026-08-21;
  `TODO.md:84-85` still carries "RULE the eight Q-rows … rulings
  owed." Twenty reds ride on them.
- **What is actually open, per row** (the semantic question + the
  cost of leaving it unruled):
  - **Q-INITSPAWN** — envelope of `go` during `$pkginit`. The memo's
    own directed probe shows gc running the child DURING init 40/40;
    "a model that releases children only at main's start excludes an
    observed behavior — observed ∉ modeled, definitionally a bug"
    (`:104-113`). Today the machine refuses the shape (honest), but
    an unruled row leaves a PROBED lower-bound gap standing and risks
    the foreclosed shortcut being built into any `$pkginit` surgery.
  - **Q-ATOMIC** — mem#atomic is a FORCED point ("behave as though
    executed in some sequentially consistent order"): the machine
    models NO atomics — 5 reds; the upper bound has a normative
    mandate with zero machine realization; FairStream/liveness and
    Q-TRYLOCK queue behind it.
  - **Q-SELSEL** — select↔select rendezvous refused
    (`Multi.lean:804/:813`); the memo notes this is Go's core
    communication idiom. Cost of no ruling: any channel-heavy real
    program (C1's lower-bound reach) hits the wall.
  - **Q-RACEPATH** — whole-cell read footprint over-refuses race-FREE
    Go (`race/free/array-read-write` red): a C2 precision debt in the
    racy-refusal soundness story (accepted-program set too small).
  - **Q-TRYLOCK** — mem#locks grants spurious failure BY NAME; the
    memo's anti-rule ("always-succeeds pin is off the menu at any
    date") is exactly the kind of narrowing a future implementer
    takes if the ruling is not on the record.
  - **Q-SYNCVAL / Q-SYNCLIT** — no latitude at all (identity
    principle / zero-value forced): 7 reds standing for want of a
    ruling on semantically-forced lowerings.
  - **Q-COND** — the valuable content is the pre-ruled envelope,
    especially NO spurious wakeups — a documented UPPER bound a naive
    prior would get wrong "in the too-wide direction where no oracle
    can catch it" (`:809-813`). Unruled, that sentence protects
    nothing.
- **FRESH re-derivation.** The memos are exactly the discipline the
  new goal demands (quoted-text envelopes, probes, decision blocks) —
  the work is DONE; only the [USER] sitting is missing, now 10 days
  old and predating the repo split. The split makes them MORE urgent,
  not less: they are pure semantics questions and this is now the
  semantics repo.
- **VERDICT: ESCALATE** — schedule the one-sitting ruling pass over
  `w32-qrow-memos.md` §RULING SHEET (rows 1-3 shape near-term work;
  4-7 cheap; 8 pre-rule-and-defer). **Claims: C1 (20 reds), C2
  (INITSPAWN probed class, RACEPATH over-refusal), C3 (ATOMIC forced
  point, TRYLOCK/COND envelope pre-rules).**

### A3-P5 — spec evolution: mechanics recorded, policy absent — ESCALATE

- **WHAT.** The language-version pin is real and disciplined AT the
  pin: spec pin = oracle toolchain = go1.26.5, "re-pin both together,
  deliberately, with the reason — never one side alone"
  (`docs/spec-sources.md:10-25`); anchor-stability and churn
  calibrated (P0 probes, `:76-91`); `scripts/check-spec-anchors`
  fails closed on rev drift; the ledger's I-5 rules the version-
  conditional reading; L-009/the 1.22 loopvar change is the standing
  reminder "language version is semantics, not packaging."
- **What is MISSING — the evolution story forward:**
  1. **No cadence/trigger/owner for moving the pin.** Nothing says
     WHEN a new Go release is adopted (each minor? each language
     version? on demand?), who decides, or what the maximum tolerated
     lag is. go1.26.6 already existed at pin time and was deliberately
     skipped for oracle agreement — correct, but that was a one-off
     [AGENT+USER] call, not a policy. A model claiming "faithful to
     Go" with an unbounded-staleness pin quietly becomes "faithful to
     Go-as-of-2026".
  2. **The re-pin re-review worklist is manual.** The designed
     workflow (campaign §8.2: covmap `recut --remap` → drift report =
     the re-review worklist of affected envelope arguments) is
     UNWIRED (A3-P2); at a re-pin today the only mechanical check is
     anchor RESOLUTION, and the go_mem `977e23a707` lesson
     (`check-spec-anchors` header) is that anchors and version lines
     survive normative changes.
  3. **The third agreement leg still does not exist**: the corpus has
     no `go.mod`, so "corpus go directive must agree" has no object
     (`spec-sources.md:22-25`, recorded at P0; still true — P3/P4
     landed without adding it).
  4. **Toolchain-derived tables ride the pin silently.**
     `tools/nativefrontend/inittask-std.tsv` (391 rows, "GENERATED …
     regenerate when the Go toolchain pin moves", header) encodes
     gc's pruned init schedule AT go1.26.5; a pin move that forgets
     the regeneration leaves the frontend modeling the OLD
     toolchain's init order with no gate that notices.
- **ORIGINAL justification.** The pin discipline was the campaign's
  4.4 decision; evolution beyond it was implicitly P5's business, and
  P5 never ran.
- **FRESH re-derivation.** Under the new goal, "incredibly well
  validated" includes validated-against-a-living-language. The cost
  of the gap is currently low (1.26.5 is near-current; anchor churn
  measured at ~13 commits per cycle) but it compounds silently, and
  the re-pin procedure has no single checklist — the obligations are
  scattered (spec-sources rule, anchor lint, census regeneration per
  `language-coverage-ledger.md:35-37`, inittask regeneration, full
  differential + baseline reasons, conformance-row Unicode tripwire
  per `g2.md:724-728`).
- **VERDICT: ESCALATE.** Concrete [USER] decisions: (a) adopt a
  re-pin cadence/trigger policy (proposal: evaluate at every Go
  minor-version release; move within one release cycle unless a
  written reason); (b) commission the single re-pin checklist doc
  that enumerates every derived artifact (S); (c) decide the corpus
  go.mod leg (S) and whether the covmap wiring (A3-P2) is a
  precondition for the NEXT re-pin. **Claims: C1-C4** (a stale pin
  eventually degrades all four).

## Full census — section 1: the stdlib-shim policy

### A3-S4 — dot-import stdlib call answers `stuck`, not a refusal — REOPEN (S)

- WHERE: `stdlibshim.go:32-43` (the header's own words: "a `stuck`
  where the fail-closed doctrine wants an explicit boundary refusal
  … the clean fix is a frontend refusal on `*types.Func` callees
  whose package is not the user package"); `emit.go:6975-6977`
  ("neither fixed nor widened"); machine answer
  `GoCore function not found: Fields` (`StepFn.lean:967`).
- ORIGINAL: found 2026-08-15 by E5's boundary probing; visible-red,
  never a wrong answer; out of E5's scope.
- FRESH: still true that it is visible-red; still a named doctrine
  deviation with a named one-line fix, now 16 days old, recorded in
  a campaign log and a code comment but NOT in BUGS.md (grep: no
  dot-import entry) — the tracking itself violates the "unclassified
  case → explicit refusal" hygiene, and a `stuck` is
  indistinguishable from an interpreter defect to a consumer.
- VERDICT: REOPEN (S — the named frontend refusal + a BUGS.md row +
  one guardrail case). Claims: C1.

### A3-S5 — the recorded per-shim deltas — KEEP (new argument), one tripwire owed

The known intentional deviations from upstream, each with its
unobservability/fail-closed argument re-checked:

| delta | where | re-derived status |
|---|---|---|
| error dynamic type name (`*pkg.goleanShimErrorString` vs `*errors.errorString`; one type PER PACKAGE vs one total) | `stdlibshim.go:333-342` | KEEP — the three-part unobservability argument (unnameable upstream type; fmt/reflect refuse; `==` type component can't flip) holds, BUT it is conditional on the modeled subset: if reflection or `%T` is ever modeled, this delta becomes observable. Tripwire owed: a one-line note at the reflect/`%T` frontier rows pointing back here. |
| strconv error TYPE (string carrier vs `*strconv.NumError`; texts verbatim) | `stdlibshim.go:106-110`, `:969` | KEEP — same argument, same tripwire (`errors.As`/`errors.Is` on NumError would expose it the day errors-package inspection is modeled). |
| %q over non-ASCII bytes, ParseUint base-0/bitSize>64, Split empty separator, dyn-fmt unmodeled verbs/kinds | throughout the shim bodies | KEEP — all route through `goleanShimUnsupported`, an interpreter-level throw user `recover()` cannot catch (`:120-132`) — verified fail-closed, correctly unrecoverable, refusal names its cause. |
| strings.Repeat output-length overflow panic NOT modeled (machine grows until fuel/memory) | `:1156-1160` | KEEP — visible stop, never a wrong answer; recorded. |
| SortFunc tie order (stable insertion sort vs upstream "not guaranteed to be stable") | `genericshim.go:21-24` | KEEP — genuine latitude, our member conforming, pinned tie-insensitively. |
| Fields/TrimSpace pin TODAY'S Unicode White_Space table | `g2.md:724-728` | KEEP — stability-listed class; the conformance rows go red under a newer toolchain "exactly as designed" — this is a real, working tripwire. |
| Builder model: String() copies vs unsafe alias; Cap unmodeled (append-growth latitude); Grow stub | `importedmodel.go:36-43` | KEEP — Cap refusal is the RIGHT call (would pin allocator latitude); copy-check panic pinned by `strings/builder-model/copy-panics`. |

Claims: C2, C3. The class survives; the OWED item is the two
conditional-unobservability tripwires (S).

### A3-S6 — what bounds the set's growth — REOPEN (fold into S1)

- The recorded bound is per-FUNCTION ("guardrail rows + fidelity
  argument FIRST", `stdlibshim.go:28`) and was honored per instance
  (W4.0/W4.1/W4.3 logs each carry the argument). There is NO
  mechanism-level bound: no cap, no retirement condition (the one
  that existed — S1 — was outgrown), no vacuity check on the five
  injection mechanisms, and no single census of the injected surface
  (this row's count — ~21 functions/methods + 2 types + ~45 reserved
  declarations — had to be assembled from four maps in
  `stdlibshim.go:148-234` plus two other files). Growth is demand-
  driven by the raft target; the north-star's stdlib appetite is the
  de-facto bound, which is not a policy. Claims: C4.
- VERDICT: REOPEN (M) — whatever S1's outcome, the policy needs: a
  tracked census table of the injected surface (one place), the
  per-shim validation floor (S2), and a stated growth rule.

### A3-S7 — fail-closed on out-of-set stdlib — KEEP (verified)

- Verified in code, all four boundaries: (i) unmodeled package-
  selector call → named refusal `package-selector call %s.%s
  (package %q surface not modeled)` (`emit.go:7522-7528`, the F-B4
  split from genuine non-method selectors); (ii) needed-shim-absent →
  `stdlib shim %s not injected` refusal (`emit.go:7285` — the
  syntactic injection scan's false-negative backstop, so scan
  imprecision fails CLOSED, `stdlibshim.go:1260-1268`); (iii)
  reserved-name collision → loud export refusal before type-check
  (`:1396-1427`, covering ALL injected names, not just keys); (iv)
  narrowings named in refusals (SortFunc `S == []E` exactly,
  `genericshim.go:52-54`; cmp.Compare floats excluded). Value-
  position stdlib references keep refusing (only the direct CALL
  shape is admitted, `:29-31`). The one hole in this story is the
  dot-import path (A3-S4). Claims: C1 — the boundary is deliberate,
  enumerated, and (modulo S4) honest.

### Policy grade, as asked

As a CLASS the stdlib-shim policy is **better than a shortcut but
below the bar the mandate sets**: the architecture (library semantics
out of the core, mock-vs-real differential, fail-closed remainder,
golden-pinned bodies) is sound and every widening carried an
argument; but the mechanism outgrew its [USER]-ruled retirement
(S1), validation depth is one-tier-per-shim where the flagship shim
got two (S2), and one recorded silent-wrong-answer channel is open
under a subject-tree assumption the new goal dissolves (S3).

## Full census — section 2: spec-truth campaign state

### A3-P1 — premise correction (finding)

The lane brief (and the memory index) say "P2-P4 did not finish
before the pivot." The campaign doc header says otherwise: P2 MERGED
`d54c8280`, P4 MERGED `c0a2c7fd` (both 2026-08-18), P3 landed
`f8ffcec8` + audit-response (`2026-08-17_spec-and-community-truth-campaign.md:27-53`).
What is actually incomplete: **P5 (the decision point with Mike)
never ran**, and each landed phase left named follow-ons (below).
The census graded those, not a phantom unfinished P2-P4.

### A3-P2 — quote fidelity unmechanized; CIPs held — ESCALATE

- WHERE: `scripts/check-spec-anchors` header ("this lint checks
  RESOLUTION only — it cannot see a resolving anchor attached to a
  misquoted or stale clause text … the audit that found five such
  quotes proves the class is real"); campaign `:14-19` ("the covmap
  content-hash layer stays validated-but-unwired until CIP-1 lands
  upstream or we decide to wrap its output (decision deferred to the
  P2 landing checkpoint)" — the deferral never resolved);
  `docs/covmap-cips/*.md` — four drafts, all "DRAFT — not yet handed
  to the covmap repo", dated 2026-08-17.
- COST to the coverage claim: every envelope argument's spec quote is
  verified only by hand at write time and at audits; a re-pin can
  change cited TEXT under a surviving anchor with no mechanical
  signal (the go_mem `977e23a707` incident is the proven instance).
  The §8.2 re-pin workflow — the whole point of the covmap
  investment — does not exist operationally (feeds A3-P5.2).
- VERDICT: ESCALATE — three [USER] decisions pending since
  2026-08-17: hand over the CIPs (outward-facing, needs sign-off);
  or wrap covmap's exit-code gap ourselves (the CIP-1 draft
  documents the exact fail-open surface); or accept manual quote
  review on the record. Claims: C3, C4.

### A3-P3 — the D-caveat and T-1: constant greens are not interpreter evidence — REOPEN (M)

- WHERE: `language-coverage-ledger.md:64-66` and rows Constants /
  Representability / Constant_declarations / Iota /
  Constant_expressions (`:115,143,152,153,200`): "constant-heavy
  greens attest go/constant delegation, not GoCore arithmetic";
  campaign `:38-44` (S3 audit): "those PASSes are spec-derivation
  checks, not interpreter evidence." T-1 (legal-line value pinning on
  the P3 literal grids) queued at `:42-44`, not done.
- FRESH: this is an honest, recorded caveat — but under the new goal
  it marks a measured hole in C2's evidence: for every corpus row
  whose observable is a compile-time-foldable expression, the
  differential compares go/constant with go/constant. What is NOT
  covered: GoCore's own runtime arithmetic on the same value grids
  (wrap points, conversion truncation, float rounding at runtime).
  The fix shape is cheap and mechanical: runtime-computed twins of
  the literal grids (route the operands through function parameters
  or a slice load so go/types cannot fold), plus T-1's value pinning.
  Note L-014 (`spec-divergence-ledger.md:393`) proves the adjacent
  channel WORKS when the values are runtime-reachable: a gc constant-
  fold bug (32-bit truncation) was caught differentially by
  grossmith.
- VERDICT: REOPEN (M — a corpus slice + T-1). Claims: C2, C4.

### A3-P4 — ledger curation and the upstream loop — ESCALATE

- WHERE: `spec-divergence-ledger.md:545-597`. Curated: 15 entries vs
  P4's shipped bar "≥20 verified entries or a recorded reason why
  fewer" (campaign §5) — no recorded reason found in the ledger or
  campaign doc; the feed-status section is honest about the counts
  but does not discharge the bar. Uncurated feed: 926 spec commits /
  372 issue refs / 212 anchors censused; the named next passes
  (Package_unsafe, 31 live commits; discussions #47141 memory-model
  rewrite and #56010 loopvar — "top curation targets") not taken.
  Upstream: L-007, L-008 spec-bugs UNREPORTED; L-014 gc-bug "UNFILED;
  upstream filing pending Mike"; campaign open question 3 (filing
  policy) "STILL OPEN, needed by P5".
- COST: the upper-bound evidence pipeline exists but idles; two
  confirmed spec errata and one gc bug sit unfiled (standing/credibility
  per the CH2O/JSTAR precedent the campaign itself cites); the
  highest-value committee-intent sources for the mem# anchors we cite
  (#47141) are un-mined.
- VERDICT: ESCALATE — this IS P5, unheld: filing policy + curation
  budget + cross-implementation lane (4.5) + conformance-synthesis
  question, each needing a written [USER] decision. Claims: C3, C4.

## Full census — section 3: owed rulings (TODO.md)

(A3-Q1, the eight Q-rows, is in the top-five section above.)

### A3-Q2 — `nonterm=` under `engine=dedup` (OQ5) — ESCALATE

- WHERE: `TODO.md:86`; `2026-08-20_w32-re-envelope-charter.md:610-635`;
  measured on the wedge (`send-then-spin`: DFS tallies 216 cut
  branches; dedup certifies {42} exhaustively at 760 nodes, nothing
  to cut).
- The OPEN question is a claim-standard one, exactly as the charter
  flagged (B-F4): what a green `engine=dedup` row ASSERTS about
  divergence. Unruled, option (c) is the de-facto state: dedup rows
  may declare a fuel "nothing on that path consumes — a number no
  gate can check" — a small fail-open in the record format (an
  unchecked declared parameter reads as checked). Riding on it: the
  membership singleton-guard exemption and the wedge row's engine.
- COST of leaving it: low today (the wedge deliberately stayed on
  DFS), but every new dedup row inherits the ambiguity, and the
  charter explicitly refused to default it BECAUSE it changes what
  green means.
- VERDICT: ESCALATE (a three-option, one-paragraph [USER] ruling;
  recommendation available in the charter — (a) or (b), never (c)).
  Claims: C4.

### A3-Q3 — the remaining W3.2 TODO items — KEEP (parks re-argued)

- **Trace-coverage push** (`TODO.md:82`) — PARKED POST-CAMPAIGN by
  [USER] 2026-08-21. KEEP as a park (it has [USER] provenance), with
  the note that under the new goal it is a C4 item (what fraction of
  the concurrency envelope the enumerating lanes actually visit) and
  belongs in Lane D's validation-apparatus grading, not silently
  behind a campaign that has since pivoted — the park's CONDITION
  ("post-campaign") is now ambiguous and should be re-stamped.
- **Slice-5 probe: print-interleaving wedge-class candidate**
  (`TODO.md:83`) — an unprobed candidate wedge class (interleaved
  print observables). Open question is empirical, cost S; leaving it
  costs one possibly-unmapped observation-surface class. KEEP as
  backlog with its S cost named.
- **Map-range pick-walk cost** (`TODO.md:87-88`, BUG-005 (L)) — the
  TODO itself rules "semantics is NOT in question"; PERF only,
  behind the both-explorers gate. KEEP.
- Note for completeness: Q-ATOMICITY (expression-step granularity,
  BUG-002's latent class) and Q-GOEXIT are F4-arc-owned
  (`w32-qrow-memos.md:18-19`) and are NOT among the eight — they are
  additional open semantic questions with no owner now that the F4
  arc has no schedule; they should appear in the master census so
  they are not lost between repos. Claims: C1, C4.

## Full census — section 4: delegation as a class

### A3-D1 — the claim shape — REOPEN (S)

- The resulting claim, stated precisely: **GoLean models the DYNAMIC
  semantics of programs that gc's own frontend (go/parser + go/types
  at go1.26.5) accepts; static semantics are claimed only BY PROXY
  of that implementation, and constant arithmetic partly rides the
  same proxy (D2).** The negative corpus's 390 compile-rejection
  rows pin gc's REALIZED rejections, not a modeled static semantics
  (an implementation-restriction "may" — I-3 — is exactly where the
  two differ).
- Where this is already stated: the language ledger's grade-D
  definition (`language-coverage-ledger.md:60-66`) is exact and
  honest — including the sentence that matters: "a differential
  divergence on it is structurally impossible" (both sides read the
  same checked program). Where it is NOT stated: the doctrine doc
  and the charter, i.e. the places an outsider reads first; grep
  finds no "static semantics"/"by proxy" sentence outside the
  ledger.
- FRESH: delegation is very likely the RIGHT TCB choice (building a
  second Go type checker is a larger, riskier artifact than the
  machine itself, and gc's checker is the de-facto arbiter of what
  "accepted Go" means). The shortcut is not the delegation — it is
  claiming "models Go" without the one-paragraph scope statement.
- VERDICT: REOPEN (S — one paragraph in the doctrine doc + README-
  level claim text, citing the ledger's D definition). Claims: C4.

### A3-D2 — go/constant leakage INTO dynamic semantics — REOPEN (M)

- WHERE the leak is: `emit.go:11` imports go/constant; `:3117` (const
  decls are no-op statements — go/types folds every USE), `:4500`,
  `:6457` ("a constant identifier folds to its value"), `:6528-6584`
  (ExactString rendering, exactRational); `mono.go:84-96` (constant
  Value preservation under substitution — a subtle spec-semantic
  decision, §4.1 of the generics note, taken on go/types' encoding).
  Every constant expression in every program is EVALUATED BY THE
  FRONTEND at emit time; GoCore never sees the arithmetic.
- Why it matters: (i) common-mode with the oracle (D1's "divergence
  structurally impossible" cuts both ways — agreement is no
  evidence); (ii) R14/U-3
  (`latitude-inventory.md:1108-1118`) is an admitted OPEN QUESTION —
  whether acceptance-relevant latitude survives at precision extremes
  "has not been analyzed"; (iii) untyped-constant → runtime-value
  conversion boundaries (representability, truncation at
  materialization) are exactly where a frontend fold decision becomes
  a DYNAMIC observable, and those rows carry the D-caveat.
- FRESH: the delegation itself should stand (go/constant implements
  spec#Constants' arbitrary-precision mandate; re-implementing it is
  a large arc with its own bug surface). What the new goal demands is
  breaking the common mode at the OBSERVABLE boundary: A3-P3's
  runtime-twin rows (the same grids computed at runtime, so GoCore's
  arithmetic is the thing differentially tested) + the R14 analysis
  (negative-lane only, S) + a recorded statement that the frontend's
  fold is part of the trusted lowering surface.
- VERDICT: REOPEN (M, shared work item with A3-P3). Claims: C2, C4.

### A3-D3 — monomorphization and the gcshape question — KEEP (new argument), residual named

- WHERE: `tools/nativefrontend/mono.go` (1,063 lines) — full
  stenciling per instantiation; identity layer reproduces
  reflect/runtime type spelling VERBATIM on the admitted surface
  (`mono.go:16-25`, pinned by reflect probes + mono_test.go);
  function-local defined types (gc's `main.score·1` internal naming)
  are REFUSED, not approximated (audit M3, `:22-25`). Generic stdlib
  desugars ride the same pipeline (`genericshim.go:8-14`).
- The question posed: gc implements generics by gcshape stenciling +
  dictionaries; we fully monomorphize — is latitude erased, and does
  the spec permit observable differences? FRESH re-derivation:
  - The spec defines generic semantics by INSTANTIATION
    (spec#Instantiations: substitution then the ordinary rules); the
    dictionary-passing translation is gc's realization strategy. For
    the ADMITTED surface (no reflect, no unsafe, function-local
    defined types refused), full monomorphization and gc's gcshape
    agree on every modeled observable, INCLUDING panic texts, which
    is exactly what the identity layer pins and the M3 refusal
    protects. The FG-line divergences are recorded where they belong
    (ledger L-002: FG dispatch ≠ gc dispatch; L-003: FGG is not
    shipped generics) — prior-art records, not model deltas.
  - So: KEEP — monomorphization is a faithful realization of the
    spec's own definition, with the observable-naming edge fail-
    closed. No spec latitude is ERASED by it (no spec sentence makes
    implementation strategy observable in the modeled fragment).
  - RESIDUAL, named honestly: mono.go + the 9,103-line emit.go are
    TRUSTED lowering with no translation validation — the injectivity
    argument for mangled identities rests on a registry backstop and
    unit tests, and the differential corpus is the only end-to-end
    check. A frontend identity-collision or substitution bug is a
    silent wrong-program class the corpus may not sample. This is
    the C4 cost the whole delegation class carries, and it is the
    thing D4 answers structurally.
- Claims: C2 (residual), C4.

### A3-D4 — what SpecTec-Go / translation-validation would change (routing note)

The SpecTec-Go direction (Mike, 2026-08-19 memory note: an AST-level
Go spec in Lean; frontend proof by translation validation; proposed
W7) is the structural discharge for every residual in this section:
D1's proxy becomes a modeled static semantics (or at least a
per-program validated one); D2's fold becomes a checked derivation
instead of a trusted one; D3's mono becomes validated per
instantiation; and the shim bodies (section 1) could become library
models stated AGAINST the AST-level spec rather than prose-contract
transcriptions. Nothing of it exists in this repo today (no doc, no
charter — the campaign doc explicitly disclaims spec-generation for
the PROSE spec, which is a different thing). Phase-3 routing: if the
census's REOPEN pile is judged heavy, W7 is the consolidation that
retires several rows at once rather than one more lane beside them.

## Unanticipated findings (outside the assigned rows)

1. **The overrides-design note is orphaned** — zero inbound citations
   for a document carrying a verbatim [USER] ruling (A3-S1). Whatever
   S1's outcome, decision-carrying docs need the same inbound-link
   hygiene the spec anchors get.
2. **BUGS.md does not carry the dot-import defect** (A3-S4) — a
   known, named, 16-day-old fail-closed-doctrine deviation lives only
   in a campaign log and a code comment.
3. **The injected-surface census did not exist until this row** — the
   full list of hand-written stdlib semantics had to be assembled
   from four maps across three files (A3-S6).
4. **`goleanShimUnsupported` is a genuinely good pattern** worth
   promoting: an injected pseudo-declaration whose CALL is an
   interpreter-level unrecoverable stop, closing the recover()-eats-
   refusals hole (R4-C-3). If shims persist, this is the refusal
   spine every future body must use; it deserves a named rule in the
   policy rather than a comment.
5. **Q-ATOMICITY and Q-GOEXIT are ownerless** after the split: F4-arc-
   owned per the memos, and no F4 arc exists on this side of the
   park (A3-Q3).
