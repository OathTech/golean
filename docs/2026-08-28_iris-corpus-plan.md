# The Iris corpus plan (2026-08-28) — THE PLAN OF RECORD for the corpus-first era

**STATUS: APPROVED — [USER] adjudication 2026-08-28 ("Great, I
approve"), on the amended revision 1 (the four-lens review's six
amendments folded).** This document REPLACES
`docs/2026-08-27_clean-proof-plan.md` (v2) as the plan of record;
v2 is then superseded-in-place with a banner (its landed content —
the W0 reset, the substrate now on main — is history, not plan; the
raft-specific unit ladder of the v3 DRAFT is superseded in
architecture but its measured pricing is reused here, cited as such).

**REVISION 1 (2026-08-28).** The four-lens professor review of this
draft returned AMEND; all six amendments are folded in below:
A1 (totality machinery: committed TotalWp adoption at U0 + the new
G-TOTAL variant unit + the restored U3.2c row + the allStreamsOk ban
for new members), A2 (the proof-side veneer tripwire unit A-TRIP —
closure checking of proof terms, since statement-closure audits and
cost profiles cannot catch span-grinding at corpus scale), A3 (the
restored named raft rows + the census-vs-corpus construct
reconciliation: five added corpus members C-16..C-20 — plus A1's
C-15 — and written scope-outs, and the corrected C-FINAL guard
framing), A4 (the G-REPR
lineage correction: Perennial's heap is flat — route (b) is the
honest analogue; the sibling-frame write test pre-registered), A5
(the G-BIND correction: the pin's `Context` class demands
unconditional laws incl. inverse decomposition — the instance route
is unavailable; re-priced), A6 (factual fixes: 123 wp laws, Fib's
Iris content, the census-claim wording, AgreementT1's
vacuous-satisfiability note, the ghost-acks consumer, the per-type
instance-generation deferred row, G-AUTO's named metrics).
[AGENT] drafter; the reviewer's findings were verified against the
pin/Perennial/census sources and are treated as ground truth; no
factual disagreement was found.

Drafter: [AGENT] Fable, design-pass worktree. Every claim below is
anchored to main @ `2a6621ed` (the triage-landed tip), the landed
docs (`docs/2026-08-27_triage-plan.md`, `docs/ARCHIVE.md`, the
prover logs), the campaign log (2026-08-27/28 entries, campaign
worktree), `docs/2026-08-28_w25-gate-postmortem.md`, the design-pass
deliverables (`2026-08-27_design-pass-findings.md`,
`2026-08-27_clean-proof-plan-v3-DRAFT.md`), the iris-lean delta scan
(`docs/2026-08-20_iris-lean-delta-scan.md`), or a fresh source read
made for this draft (file:line cited inline). [AGENT] judgment and
estimates are marked; [USER] decisions are cited to their log
entries.

---

## 1. The architecture of record

Stated by the [USER] 2026-08-27 (campaign log, "[USER] architecture
statement + the pattern-corpus aim"; template = the cerberus-lean
sibling, RefinedC/BRiCk-analogous), and made the strategy of record
by the [USER] corpus-first decision the same day ("Raft as a target
is just too loose to make delivery possible" — raft becomes the
FINAL corpus member; the delivery unit is the corpus case, not the
campaign):

```
  Executable GoCore        — the TCB and statement referent; our
      ⇧ adequacy             distinctive strength: executable +
      ⇧ layered              oracle-tested (differential corpus)
  Relational semantics     — the per-step relation + the language
      ⇧ layered              instance a WP is defined over
  Iris reasoning           — THE BUILD: heap RA, WP, FnSpec
      ⇩ applied to           contracts, per-construct symbolic
  Target programs            rules, assertion layer, case-split,
                             automation → canonical-property
                             theorems per corpus program
```

Where each existing asset sits (all verified on main @ `2a6621ed`):

| tier | asset | status |
|---|---|---|
| 1 (TCB) | `stepFn`/`execStmt`/`runProgramM` + differential corpus + reflection pair + Surface first-order judgment layer (`GoTriple`/`GoSpec`/`GoFuncSpec`, Iris-free) | trusted, unmoved |
| 1→2 | `MachineSound.lean`: `stepFn_sound` / `step_complete` — total two-way per-step correspondence, pinned | HAVE |
| 2 | `Machine.Step` (155 ctors) + `Steps`; nondeterminism = demonic rule multiplicity (tape stays at tier 1) | HAVE, raft-ready — a census-INFORMED scout claim (the census has no per-construct vocabulary; the tier scout found no sequential construct gap against the raft fragment; re-checked construct-by-construct at gate N-3's reconciliation, §6.2) |
| 2→3 | `Lang.lean`: bare `Language` instance over `Step` (no evaluation-context structure — the G-BIND gap) | HAVE/partial |
| 3 | genuine iris-lean (pin `3877dbec`): gen_heap state interp (`Ghost.lean`), 8 lifting lemmas, 123 `wp_*` laws in the 11 `Laws/*` files (declaration count: `wp_`-prefixed theorems, review re-grep — the draft's 129 double-counted witness siblings), 4 adequacy theorems (`Adequacy.lean`), `go_walk` tactic, non-vacuity witness gate | HAVE at function scale; 7 structural gaps (§4 — the seventh, totality machinery, review-discovered per A1) |
| 3→1 readout | adequacy exits to `execStmt`/`stepFnIter` (`SurfaceExit.lean`), NOT yet to `runProgramM` (the G-EXIT gap); `RunGlue` + `InitSpec` are the landed halves of that last step | partial |
| statements | the 51-name designated set (`Audit.lean:290`), template = the Surface FnSpec family over real etcd raft quorum code | HAVE; the corpus extends it |
| substrate | plug family (+`PlugWitness`), crossing kit (+`CrossingWitness`), `MapPerm`/`MapPermRead`, readers (`AbsTwinCheckerRead`), ghost-acks (`NativeObligations`), `RunGlue`, `InitSpec`, archived invariant clause inventory | landed 2026-08-28, each with a named consumer unit below (ghost-acks' consumer = the restored U3.2b row, §5.3 — the certified/`leaderCommitOk` discharge) |

The CallSpec parallel calculus is dead and archived
(`archive/callspec-era`; `docs/ARCHIVE.md` §"The CallSpec era" —
harvest pointers only, never cited by a proof).

---

## 2. The target theorem set

The reasoning's pin-down: three layers of statements, and the rules
that make cheating hard.

### 2a. The designated TCB sentences (per corpus program)

The **Surface FnSpec idiom is the template** — it is what the 51
designated names already look like and it satisfies the Audit gate's
mechanized deletion test (`Audit.lean:127`: designated statement
closures must be Iris-free AND relation-free; they speak
`stepFn`/`execStmt`/`runProgramM` only). The working shape
(`Surface.lean:489`):

```lean
def GoFuncSpec (types funcs methods) (fid : FuncId) (kind : IntKind)
    (args : Array Expr) (P : HProp) (Q : Int → HProp) : Prop :=
  ∀ (ra : Nat) (w : GoValue),
    GoSpec types funcs methods [[("$callres", Loc.base ⟨ra⟩)]]
      (.sep (.pointsTo ra ⟨some (.int kind), w⟩) P)
      (.call #[.var "$callres"] fid args)
      (.ex fun n => .sep (.pointsTo ra ⟨some (.int kind), .int n kind⟩) (Q n))
```

(`GoSpec = GoTriple ∧ ProgressExec` — the triple carries frame
preservation in the statement; multi-result sibling `GoFuncSpec2`.)

**Every corpus program ADDS, on the model of the quorum pilots
(`quorumOneKnown*`, `Challenge.lean`):**

1. a **FuncSpec-analogue** designated sentence (`GoFuncSpec`/
   `GoFuncSpec2`/`GoSpec` over the pinned lowered program; for
   whole-program members — the init case and raft — the sentence is
   `runProgramM`-shaped via G-EXIT, the `AgreementT1` shape);
2. a **first-order readout** corollary (run-conditioned: any `.ok`
   run exhibits the concrete answer — the `quorumOneKnownReturnsTwelve`
   shape);
3. a **negative twin** (the `goldenNotThree`/`quorumOneKnownNotEleven`
   shape: the spec refutes a wrong answer — the vacuity/triviality
   guard on the spec itself);
4. **totality where apt**: a `Terminates`/`GoSpecT` form and/or a
   `TotalReadout` (∃-fuel) sentence, per the existing quartets.

**Designation acts are [USER]-only**, per standing doctrine: the
drafter POSES sentences; the [USER] designates; every designation
change triggers the comparator-judge (anchor: 51 theorems certified
in 122 s on a fresh clone at the triage landing — cheap enough to
run per batch, so designations are batched per corpus wave, §6).

### 2b. The Iris-internal counterparts

For each TCB sentence, a WP triple at tier 3 whose **adequacy
readout IS the sentence**: `⊢ WP c {{ Φ }}` (stated with the §4
assertion layer: per-field points-to, `own_slice`/`own_map`
carriers, FnSpec contracts) discharged through
`go_adequacy`/`go_heap_adequacy_own` → the Surface exit doors
(`goSpec_of_wp`, `SurfaceExit.lean:96`) → (for whole-program forms)
`RunGlue`'s `runProgramM_readout_of_total`. The Iris statement is a
proof device, never a statement dependency — the Audit deletion test
enforces this mechanically.

### 2c. The raft summit sentences

The `AgreementT1` family refresh is **the final corpus member's
designation** (unit G-STMTS): `AgreementT1` (∀ fuel ch r partial
form — already a pinned Prop, `Specs/RaftAgreement.lean`), plus the
drafted `TotalT1` (∀ ch, ∃ fuel r, ok ∧ spec) and `NeverFaults`
(corollary via `runProgramM_classify_of_total`) — the v3-DRAFT §0
shapes, unchanged by the architecture reset. Posed at drafting,
designated by the [USER] at the raft member's ceremony.

Stated honestly (A6): the partial form `AgreementT1` (∀ fuel ch r,
`ok → spec`) is **vacuously satisfiable** — a system that never
reaches `.ok` satisfies it. Its non-vacuity is carried entirely by
`TotalT1` (∃-fuel `.ok` on every stream), which is why the recorded
end-state doctrine makes the TOTAL form the designated sentence and
the partial form its decomposition; the designation batch treats
them as a pair, never the partial form alone.

### 2d. The anti-cheating invariant (standing, era-wide)

- **Every corpus case ships its negative twin** (2a.3). A spec whose
  negative twin cannot be stated or proved is not accepted as a
  closure.
- **Proofs go through the WP calculus.** The corpus exists to
  exercise tier 3. The named forbidden pattern of the era is
  **span-grinding inside a WP proof**: a proof that drops through
  adequacy (or unfolds the interpreter directly) to grind kernel
  spans of the concrete run under an Iris wrapper is a VENEER —
  the banned concrete-walking method in costume — and fails review.
  Two honest limits of the existing defenses (A2, review-verified):
  the Audit gate polices STATEMENT closures only (its own license:
  "Proofs may use anything"), and cost profiles cannot discriminate
  at corpus scale — kernel grinding is CHEAP on 15–60-line
  programs, so a veneer would be a cost INLIER, not an outlier.
  Negative twins do NOT serve this function either: a veneer proves
  a twin exactly as easily as the positive. The mechanized defense
  is the **veneer tripwire unit A-TRIP** (§6.3): a PROOF-SIDE
  closure check for tier-3 corpus lemmas — the proof term may reach
  `stepFn`/`execStmt`/`stepFnIter`/`allStreamsOk`/kernel-decision
  constants only through the Laws/lifting/adequacy layer, never
  directly.
- **Bounded techniques stay banned** (charter): no fixture-anchored
  statements, no enumeration-as-∀; program-text shape constants in
  ∀-quantified rules remain the recorded carve-out.
- **New corpus members may NOT prove `Terminates` via the
  `allStreamsOk` decide+kernel route** (A1): every landed
  Terminates today is fuel-bounded enumeration on pinned seeds —
  exactly the bounded technique the charter bans as proof for new
  work. New totality sentences discharge SYMBOLICALLY through
  total-WP + the G-TOTAL variant rule. The existing pilot quartets
  are grandfathered as labeled scaffolding (retirement condition:
  re-proved through G-TOTAL when their programs are re-specced, or
  retired with the gallery-row cleanup).
- **The quantifier audit governs every unit** (each §4 unit opens
  with its line). The era's end-sentence quantifiers and their
  discharging rules:

| quantifier (per corpus sentence) | discharging rule | unit |
|---|---|---|
| subject identity | reflection pair (wire + shape pins) | HAVE |
| ∀ initial states in P (footprint family) | representation predicates + frame (separation) | G-REPR |
| ∀ caller contexts / frames | `wp_bind`/fill + the frame rule (GoTriple carries the frame in-statement) | G-BIND |
| ∀ ch — schedule/latitude | tier-2 demonic rule multiplicity, erased at adequacy (by construction); order latitude via Perm-of-draws conclusions | HAVE / G-MAPITER |
| ∀ iterations | loop-invariant laws (`wp_while_inv`, map-range law) | HAVE / G-MAPITER |
| ∃ fuel (totality) | total-WP (upstream `TotalWeakestPre`/`TotalAdequacy`, adopted at U0 — A1) + the variant-carrying loop rule (G-TOTAL, §4.7) + RunGlue's classification glue | U0 + G-TOTAL (rules that will exist; today NO variant machinery exists at any tier — review-verified) |
| whole-program ∀ fuel ∀ ch | `runProgramM_mono`/`_readout_of_total` joined to WP-at-entry | G-EXIT |

"By instances" is never an answer, per charter.

---

## 3. Unit 0 — the iris-lean refresh + reuse survey

**The [USER] backlog item (2026-08-19: "update the pin + reuse
survey — their abstractions/automation vs our ad-hoc; pin move = its
own small arc"), now on the critical path**: the corpus era's
throughput lives or dies on proof-mode ergonomics, and the upstream
delta contains exactly the ergonomic layer we would otherwise
hand-build.

*Quantifier-audit line: interface/infrastructure — advances no
quantifier, and says so. LINEAGE: we inherit before we build — the
entire unit is the lineage discipline applied to our own base
library.*

### 3a. Pin assessment (what we have TODAY — re-verified this draft)

Pin `3877dbeccd…` (2026-06-25), wired via `proofs/lakefile.toml` +
manifests, reading copy `deps/iris-lean` in sync (the `setup-deps`
gate enforces this). The pin is substantially more complete than the
"BI library" framing suggests — re-verified by direct read:

- **Full MoSeL proof mode** (`Iris/ProofMode/*`): ~30 `i*` tactics,
  pattern parsers, spec-application syntax.
- **Cameras/RAs**: OFE/CMRA/Auth/View/Frac/DFrac + `Algebra/Heap`,
  `HeapView` (gmap_view analogue), and — decisive — **`BI/Lib/GenHeap`
  with `pointsTo l dq v`, the full lemma suite, and meta tokens**.
  Our `Ghost.lean` already instantiates it.
- **The language interface**: `Language`, **`EctxLanguage`/
  `EctxiLanguage`, `Context K`** classes, `wp` with **`wp_bind`**,
  the lifting families (`Lifting.lean`, `EctxLifting.lean`),
  adequacy (`wp_strong_adequacy_gen`), and a worked HeapLang
  instance including a Qq-based evaluation-context finder tactic
  (`HeapLang/Tactic.lean`) — the structural template for G-BIND and
  G-AUTO. Caveat (A5, review-verified): the `Context K` class
  demands three UNCONDITIONAL laws including the inverse
  decomposition `primStep_fill_inv`, so having `wp_bind` in the
  library does not make G-BIND an inheritance — §4.1 carries the
  honest obligation shape and price.

The pin's real gaps: no telescopes → no Texan-triple notation; only
`wp_bind`/`wp_pure(s)`/`wp_rec`-class tactics (heap-step lemmas are
`iapply`-by-hand); `TotalWp` is an UNINHABITED notation class — no
instance, no lifting, no adequacy, no laws (A1, review-verified):
without the upstream total-WP theory, no totality rule exists at
any tier.

### 3b. Upstream delta (from `docs/2026-08-20_iris-lean-delta-scan.md`
— 135 commits, zero divergence, fast-forward; **re-run the head
check at unit open**: the scan is 8 days old and an upstream 4.33
bump was in flight)

What the delta buys THE BUILD (the corpus era changes the payoff
table — the 2026-08-20 scan priced the delta against the
channel-logic resume; today the same rows pay into §4 directly):

| upstream item | pays into |
|---|---|
| `AddModal`/`ElimAcc`/`ElimModal` instances for WP | kills the modality dance (393 `fupd_intro` sites, `go_walk_dance`) — raw G-AUTO throughput |
| `iinv`, `iinduction`, `ieval`/`isimp`/`iunfold`, completed intro/spec patterns, `iframe` w/ existentials | G-AUTO tactic base |
| `frame_pointsto`, `CombineSepGives/As` points-to instances | G-REPR ergonomics (field points-to splitting/combining) |
| telescopes + Texan triples | the FnSpec-contract notation decision (§4.3) |
| `TotalWeakestPre`/`TotalAdequacy`/`TotalLifting` | **COMMITTED ADOPTION at this unit (A1 — not an assessment)**: the era's entire totality story (§2d's ∃-fuel row, G-TOTAL, every new `Terminates` sentence) sits on this theory; our lone `Specs/TotalPins` carry re-seats on it |
| `big_sepM2`, `ghost_var`, `gset_bij`, `SavedProp`, later credits | G-REPR/G-INV vocabulary as needed |
| `equiv_iff_eq` (extensional maps) | retires hand extensionality in `HeapBridge` |

Adopt-vs-build rule for the whole unit: **inherit before we build**;
a keep-ours row requires a stated reason (the 2026-08-20 scan's own
DONE criterion — its keep-ours rows R4/R11/R13 stand: the pool
carrier, `go_walk`'s language-agnostic law table, the fork/join
specs).

### 3c. Costs and the trust-tool edge (honest)

- **Toolchain bump** Lean v4.31.0 → v4.32.2 (or the boundary rev's
  requirement) across all four `lean-toolchain` files — the dominant
  cost; plus the measured-in-advance "silent class": instance-
  priority/synthesis changes that flip which instance fires under
  `go_walk` — **budgeted explicitly**, per the scan.
- **Comparator/lean4export re-pin**: the judge's replay toolchain
  must match. The [USER] pre-approved the CONDITIONS 2026-08-20
  (version move only, sources pristine, old→new + rebuild provenance
  recorded, judge re-runs on a known-good landmark) — but per the
  trust-tools rule the move itself still executes only with
  at-the-moment [USER] approval (§6, gate N-2).
- 19 direct Iris-importer files to fix mechanically; the parked
  channel-logic lane rebases through the move, not across it
  (recorded in the park row).

**Price ([AGENT]): 2–3 sessions** (pin move + toolchain as one
gated commit ≈ 0.5–1; the instance-priority tail across the 240
transitive files ≈ 0.5–1; the reuse-adoption slice — modality
instances wired into `go_walk`, plus the COMMITTED total-WP
adoption: `TotalWp` instance for our `Language`, total lifting
wired, total adequacy readout checked against `ProgressExec` —
≈ 1) + the judge landmark re-run. Deliverables: the moved pin green
in its own commit; the reuse table promoted from draft with a
reason on every keep-ours row; the comparator re-pin executed under
its conditions; **the total-WP theory inhabited for our language
instance** (G-TOTAL's prerequisite).

**Consumers: every unit in §4** (G-AUTO most directly), plus the
channel-logic resume's named condition (i) — this unit discharges it
for that later road too.

---

## 4. The structural ladder

One unit per gap from the triage plan's §5.3 gap table — plus
G-TOTAL (§4.7), the totality gap the review found the gap table
itself had missed (A1) — each priced
against the measured anchors (v3-DRAFT §2, derivation-anchored:
straight member ≈ 30–60 min; kit-crossing member ≈ 1–2.5 h; 11
members ≈ 1 worker-session; one mechanism unit ≈ 0.5–1.5 sessions;
the W2 plug class = 2,948 lines in 1 session, probe-first). Each
unit's DONE = **its corpus gate instance closes through the layer**
(the W2 gate discipline, re-aimed at corpus programs — §5 names
them).

### 4.1 G-BIND — the bind/fill unit (the landed plug theorem wired as `wp_bind`)

*Quantifier-audit line: ∀ caller contexts, by the bind/fill rule —
never by per-arity instances. LINEAGE: Iris `EctxLanguage`/`wp_bind`
(evaluation-context lifting); `plugK` is the fill function; Perennial
analogue: GooseLang's `LanguageCtx'`/`ectx_lang_ctx'`.*

- **The gap**: `Lang.lean`'s instance is bare CEK — no
  `EctxLanguage`, no `wp_bind`; every call today goes through
  per-arity enter laws (`wp_call_enter₁₁/₂₁/₂`, `Laws/Call.lean`)
  with self-disclosed "widening owed" notes (`Laws/Call.lean:471,880`).
- **The input, landed and waiting**: the plug family — `plugK`/
  `plugC` (fill), `hasBarrierK` (the barrier recognizer),
  `stepFn_plug` (per-step fill/step commutation over every arm, with
  the complete non-locality census: `mapIterFree` +
  `recoverThroughWrappers` are the only context-inspecting
  features), `callSpan_plug` (span-level bind), plus `PlugWitness`.
  The W1 probe finding (FrameSim structurally cannot deliver caller
  env/k) is the standing design constraint.
- **Obligation shape** (corrected per A5, review-verified against
  the pin): the pin's `Context K` class demands three UNCONDITIONAL
  laws, including the inverse decomposition `primStep_fill_inv` —
  a premise-conditioned `plugC` cannot be a typeclass instance, so
  the "inherit `wp_bind` from the library" route is UNAVAILABLE as
  an instance route. The honest shape: (i) transport the
  `stepFn_plug` commutation to `Step` (case-transport —
  `MachineSound.lean`'s arms mirror `Step`'s constructors 1:1 and
  share premise functions verbatim); (ii) **the inverse half is a
  NEW obligation**: `stepFn_plug` is forward-only (fill-then-step),
  and a bind law also needs step-then-decompose — the fill-step
  INVERSION under the barrier premises, not yet proved in any form;
  (iii) state the direct bind lemma
  `WP c {{ _, WP plug-continuation }} ⊢ WP (plugC … c)` — either
  with per-`k'` hand-built `Context` terms passed explicitly (the
  library-shape variant of the same work) or as a standalone lemma;
  both are the (b) shape. Retire/absorb the per-arity widening-owed
  notes as corollaries.
- **Gate instance**: corpus case **C-05 `callchain`** (§5) — a
  nested static call with a defer, proved once through `wp_bind`
  at an open caller context (also discharges `PlugWitness`'s
  recorded retirement condition and replaces the killed W2Gate
  composition demo, closing that accepted gap).
- **Consumers**: G-CALLS (kills the per-geometry surface), every
  corpus case with a call (all of them), the raft member.
- **Price ([AGENT], W2 anchor, re-priced under A5)**: 1.5–2
  sessions, probe-first — the inverse-decomposition obligation is
  new proof content the W2 forward walk did not pay for; the probe
  (two arms of the inversion before the walk) prices the rest.

### 4.2 G-REPR — the assertion layer (whole-cell heap → per-field points-to; THE BIG ONE)

*Quantifier-audit line: ∀ initial states in the footprint family, by
representation predicates + the frame rule — the ∀-state quantifier
of every FnSpec precondition discharges here, and placement
genericity (∃-address) replaces the `_ren` transport spine. LINEAGE:
separation-logic representation predicates (Reynolds/O'Hearn);
Perennial New Goose `TypedPointsto`/`IntoValTyped` (per-type
primitive laws as class fields; struct points-to DEFINED as the ∗ of
field points-to at pure `struct_field_ref` offsets; `Access` classes
bridging whole-struct and per-field views; sealed `own_slice`/
`own_map` carriers) and RefinedC type assignment; BRiCk `Rep` for
the ptr-indexed-predicate alternative.*

- **The gap**: the heap RA is base-address-only whole-cell —
  `HeapBridge.lean:26-48` soundly drops field/index keys; one `↦`
  owns an entire nested struct; no `own_slice`/`own_map`/
  `own_struct`; no per-field framing. This blocks every deep-struct
  program (raft's `r.raftLog.storage…` chains, clone/copy, per-field
  mutation under a frame).
- **Obligation shape** (design decision inside the unit, probed
  before the walk is paid; route framing corrected per A4,
  review-verified against the Perennial source): Perennial's New
  Goose heap is FLAT — per-field points-to ARE `heap_pointsto`
  facts at distinct locations, the struct assertion is a
  separating conjunction over disjoint locations, and NO
  fractional-lens-over-a-cell construction exists there. Therefore:
  (b) **re-key route** — re-key the ghost heap at (base, path) so a
  per-field points-to IS a gen_heap points-to over disjoint keys —
  **is the honest Perennial analogue and the presumptive route**;
  (a) the **whole-cell view route** (fractional lens predicates
  over the base cell) is retained only as the probe's comparison
  arm, with its structural defect stated up front: a fractional
  view of one cell CANNOT deliver a per-field WRITE while a frame
  holds a sibling field of the same struct (writing needs the full
  fraction of the cell).
  Either way tier 1/2 are untouched (the assertion layer is
  ghost-side).
- **The probe's pre-registered discriminating test** (A4): write
  one field of a struct while the frame holds a points-to for a
  SIBLING field of the same struct. A candidate that cannot state
  and prove this is a reader-predicate in costume and fails the
  probe regardless of what else it proves.
  Products either way: `own_struct`-style per-field decomposition
  with pure field-offset addressing, `own_slice` (+cap), `own_map`
  (the `gmap`-carrier ownership the map laws speak), ∃-address
  genericity in specs, and the landed readers (`AbsTwinCheckerRead`)
  re-seated as the pure projections of representation predicates.
- **The [USER] footprint insight rolls up here** (ruling of
  2026-08-28, recorded verbatim: "I expect this kind of
  choice-invariance will just roll up into the reasoning layer, eg.
  when we have a points-to we don't care about choices outside the
  footprint"): allocation-placement and capacity-slack latitude
  outside a spec's footprint is frame-irrelevant BY CONSTRUCTION
  once ownership is footprint-shaped — the separation discipline
  subsumes the erasure instrument. This is why `ChoiceCanon` dies in
  the hygiene slice (§6.3) with no successor obligation.
- **Gate instance**: corpus case **C-08 `protoclone`** (deep-struct
  clone: per-field points-to split, copied footprint, frame intact)
  + **C-13 `initchain`**'s nested field-chain read (its PC-13 half).
  DONE = both closed through the layer with specs stated in
  per-field vocabulary, **AND C-08's spec includes a
  write-under-sibling-frame obligation** (A4: the clone must WRITE
  destination fields while the frame holds sibling points-to — a
  read-only clone spec could pass under a reader-predicate in
  costume and does not gate the unit).
- **Consumers**: G-INV (heap half of every invariant clause),
  G-CALLS ((T,error) result cells), G-MAPITER (`own_map`), most
  corpus cases, the raft member end-to-end.
- **Price ([AGENT], honest)**: the largest single design unit of the
  era — **2–4 sessions**, structured as: measured design probe (the
  (a)/(b) referee — one small struct program under each candidate,
  compare) ≈ 0.5; the carrier + access-lemma algebra ≈ 1–1.5; the
  `own_slice`/`own_map` carriers + law re-statements ≈ 1; reader
  re-seating ≈ 0.5. Variance is real: this is the unit most likely
  to force one redesign loop (budgeted, the W1-pilot pattern).

### 4.3 G-CALLS — function-value dispatch + the call-law family

*Quantifier-audit line: ∀ states at call boundaries and ∀ arities/
result shapes, by n-ary call laws over list-indexed allocation —
never per-(arity × result-count) instances. LINEAGE: Hoare
procedure-call rules; GooseLang `wp_call`/`wp_func_call`/
`wp_method_call`; the FnSpec contract as the spec carrier.*

- **The gap**: call laws hardcoded per (arity, result-count); alloc
  cores fixed 1–4 cells ("list-indexed generalization stays owed",
  `Lifting.lean:246,309`); no composed law for func-value-FIELD
  dispatch (raft's `r.step`, reached on every handler delivery);
  `(T, error)` returns unservable.
- **The input**: G-BIND (the frame-entry geometry collapses to one
  bind + one enter law); the **four machine-geometry facts**
  harvested from the CallSpec era (`docs/ARCHIVE.md` "Harvest
  pointers", each probe-anchored in a landed log): (1) defer-free
  callees end at `.returning (.frame …)`; (2) deferred callees exit
  via `.next (.frame …)` and NEVER re-visit `.returning` — both
  arrival arms perform the same next step, so one arrival
  abbreviation serves both; (3) the wrap-per-op normalize rule; (4)
  `postOp`/`opDone` is a pure strip. These are facts about `stepFn`
  itself and price the law statements before proving starts. The
  cancelled CallSpecV's site census (w3-m park record) prices the
  func-value surface.
- **Obligation shape**: `wp_call_enter`/`wp_frame_return` over
  list-indexed allocation (n-ary); the two-geometry return law
  (one law over the shared arrival shape); the func-value-field
  composition law (field read ∘ `callValArgsK` entry); `(T, error)`
  multi-result return into per-field-owned result cells (needs
  G-REPR's result-cell vocabulary).
- **Gate instances**: **C-07 `stepfield`** (the `r.step` shape in
  miniature — func-value field dispatch) and **C-12 `finderr`**
  ((T, error) return with the error-global trichotomy).
- **Consumers**: every corpus case with method/interface calls
  (C-06, C-11), the raft handler tier.
- **Price ([AGENT])**: 1–2 sessions (triage anchor), after G-BIND.

### 4.4 G-MAPITER — the map-range law (the MapPerm carrier lands its consumer)

*Quantifier-audit line: ∀ iterations AND ∀ draw orders (the demonic
map-order pick), by a loop-invariant law with a Perm-of-draws
conclusion — order is the family parameter, never an enumerated
case list. LINEAGE: loop invariants + multiset abstraction (the (M)
design note's recorded lineage — the carrier is never canonicalized;
the quotient lives in spec vocabulary); Perennial `wp_map_for_range`
with `own_map` ownership + `for_map_postcondition`.*

- **The gap**: `wp_map_iter_inv` is key-only, mutation-free,
  order-silent (`Laws/Range.lean:190-193,403-405`, limits
  self-disclosed); raft's `for k, v := range` loops and the driver
  pick loop need key+value binding, stop admission, mutation
  tolerance, and a Perm-of-draws readback.
- **The input, landed and waiting**: `MapPerm` (932 lines — the Perm
  algebra: `lookupP_perm`, `sortedLT_eq_of_perm`, the value-generic
  pick-step family, `mapPickLoop_perm` with the tape-suffix
  conclusion) + `MapPermRead` (the decode transports —
  **scaffold-labeled, zero consumers, discharge OWED at this unit**
  per the in-tree label and `ARCHIVE.md`'s honest no-live-replacement
  record for `mapPickLoop_perm`) + the MapLoops width facts.
- **Obligation shape**: `wp_map_range_inv` (key+value,
  stop-admitting, mutation-tolerant, demonic order) over the G-REPR
  `own_map` carrier, concluding the invariant + a Perm-of-draws
  fact; the soundness content is exactly MapPerm's algebra lifted
  through the lifting layer.
- **Gate instances**: **C-01 `mapwalk`** and **C-09 `miniids`**
  (which is ALSO the owed `mapPickLoop_perm`/`MapPermRead` discharge
  site — the scaffold labels retire here, on schedule).
- **Consumers**: C-02, C-11, the raft driver pick loop and Progress
  iteration, G-SORT.
- **Price ([AGENT])**: 1 session (triage anchor; the algebra is
  done — this is the law statement + lifting + the two closures).

### 4.5 G-EXIT — the whole-program readout (adequacy → `runProgramM`)

*Quantifier-audit line: the whole-program ∀ fuel ∀ ch quantifiers,
by `runProgramM_mono`/`_classify_of_total`/`_readout_of_total`
joined to a WP at the entry configuration — never by fuel-pinned
runs. LINEAGE: Iris adequacy (the readout is a theorem, not a
convention); the ∃-discharge of the setup boundary is the charter's
sanctioned concrete-evaluation carve-out (`InitSpec`).*

- **The gap** (confirmed by direct read this draft): all four
  adequacy theorems conclude `adequate .NotStuck c σ φ` over
  `Config`/`ExecState`; the Surface exit doors land on `execStmt`
  (`SurfaceExit.lean:96`); the designated whole-program sentences
  are over `runProgramM` (`Specs/RaftAgreement.lean`). The last
  step — setup + `$pkginit` + entry wiring — is unproved as a
  chain.
- **The input, landed and waiting**: `RunGlue` (the ∃N-total ⇒
  ∀-fuel-partial readout + truncation classification, 18 pins) and
  `InitSpec` (`initSetup_establishes`: ∃F₀ ∀fuel≥F₀ ∀ch, the setup
  phase reaches the entry-frame boundary, statics loaded,
  stream-untouched).
- **Obligation shape**: the join theorem family — WP at the entry
  config (+ the heap-ownership seeding from
  `go_heap_adequacy_own`'s `[∗map]` initial heap) ⇒ a
  `runProgramM`-shaped sentence; packaged as a `GoProgramSpec`
  template so whole-program corpus members state one designated
  sentence each; the NeverFaults corollary engine
  (`runProgramM_classify_of_total`) exposed as its standard
  corollary.
- **Gate instance**: **C-13 `initchain`** (globals seed + `$pkginit`
  + constructor cascade + a one-line main) — the first
  whole-program corpus sentence proved end-to-end through the
  layer.
- **Consumers**: G-STMTS (the raft sentences), C-13, the raft
  member.
- **Price ([AGENT])**: 0.5–1 session (triage anchor; both halves
  landed).

### 4.6 G-SORT — the symbolic sort law (small)

*Quantifier-audit line: ∀ states at sort call sites, by one
packaged law — the per-call-site effect premise re-proof
(`Laws/StmtOps.lean:672-681`) retires. LINEAGE: permutation
specifications (sortedness + Perm — the classical sorting spec);
consumes `sortedLT_eq_of_perm`.*

**Named prerequisite (A3, restored from the v3 ladder's V-Sort
row): the `slices.Sort` lowering census** — the (M) note recorded
that `slices.Sort` has no lowered body under that name in the wire
(w3-m log, machine finding vi); a small read-only census against
the wire establishes what the sort law's subject actually is,
BEFORE C-09's Go source is finalized (N-3 depends on it). Gate
instance: **C-09 `miniids`** (shared with G-MAPITER — build map →
collect → sort). Price ([AGENT]): 0.5 session including the
census, after G-MAPITER.

### 4.7 G-TOTAL — the variant-carrying loop rule (A1: the totality machinery that does not yet exist)

*Quantifier-audit line: ∃ fuel (the totality quantifier of every
`Terminates`/`TotalReadout`/`TotalT1` sentence), by a total-WP loop
rule with a DECREASING MEASURE — never by fuel-bounded enumeration
(`allStreamsOk` decide+kernel is banned for new members, §2d).
LINEAGE: Floyd variants / total-correctness Hoare logic; Iris total
weakest precondition (upstream `TotalWeakestPre`/`TotalAdequacy`/
`TotalLifting`, adopted at U0); Perennial's total-wp analogue.*

- **The gap (review-verified, A1)**: no variant machinery exists at
  ANY tier today — `wp_while_inv` is Löb-based and measure-free
  (admits divergence), the pin's `TotalWp` is an uninhabited
  notation class, `GoSpecT` has zero inhabitants, and every landed
  `Terminates` is decide+kernel on `allStreamsOk` (fuel-bounded
  enumeration on pinned seeds). The plan's totality claims were
  naming rules that did not exist; this unit builds them.
- **Obligation shape**: instantiate the adopted total-WP for our
  `Language` (U0 delivers the theory; this unit inhabits the
  program-logic side): a total-WP while/loop rule carrying an
  invariant + a decreasing measure (variant), total lifting for the
  step relation, and the total-adequacy readout joined to
  `ProgressExec`/`Terminates` and (via RunGlue) to the ∃-fuel
  whole-program forms.
- **Gate instance**: **C-15 `countloop`** (§5.2 — a while loop with
  a decreasing counter) proving its `Terminates` SYMBOLICALLY, plus
  the total form of **C-01 `mapwalk`** (measure = undrained keys)
  as the map-range width check.
- **Consumers**: every totality sentence of the era; `TotalT1`; the
  restored U3.2c measure row (§5.3) is its raft-scale continuation.
- **Price ([AGENT])**: ~1 session after U0 (the theory arrives
  ported; the work is our instance + the loop rule + two closures).

### 4.8 G-AUTO — the automation probe and build-out (the throughput referee)

*Quantifier-audit line: advances no quantifier — it is the measured
guard that the OTHER units' rules are actually usable at corpus
throughput (middle-path rule: measured fragility/cost, never
hypothetical). LINEAGE: tactic-driven WP automation — HeapLang's
evaluation-context finder (already in the pin,
`HeapLang/Tactic.lean`) + Goose's `wp_auto`/`wp_apply`/`wp_start`
Ltac2 ladder as the shape reference; the judgment-driven
RefinedC/Lithium alternative is EXPLICITLY the road not taken for
now ([AGENT]: it depends on typeclass-resolution-as-Prolog and a
bespoke interpreter — a much larger port; revisit only if the
tactic route measurably stalls, with a probe refereeing).*

- **The gap**: `go_walk` stops at invariant rules, nondet branches,
  real store obligations, resource splits (`Tactics/GoWalk.lean:51-64`);
  u64 side-conditions are hand-`omega`; the largest shipped Iris
  walk is ~2 functions (`GoldenQuorumWP`, 1,512 lines) vs corpus
  cases wanting function-per-hour throughput.
- **THE PROBE (before any corpus-wave charter)**: re-prove ONE
  landed Surface case (a quorum pilot) and prove ONE new case
  (C-03 `lockstat`) with the post-U0 tactic base; compare against
  the archived CallSpec datum (30–60 min straight / 1–2.5 h
  crossing members; 11 members per session) — the layer must beat
  or match the dead calculus's measured throughput at equal
  honesty, or the build-out backlog reorders before cluster spends.
  **Collected metrics, named (A6)**: wall time per case,
  proof-lines-per-program-line, manual steps per construct, and
  automation coverage (fraction of proof steps discharged by
  `go_walk`/successors without hand intervention). A branch-scale
  criterion rides the probe: the raft dispatch is a ~20-arm switch,
  so the probe's report states how the per-construct costs
  extrapolate to that arm count (a scale test, not a corpus
  member). Veneer detection is NOT this probe's job (A2: at corpus
  scale a veneer is a cost inlier) — that is the A-TRIP closure
  check (§6.3).
- **Build-out backlog (sized by the probe, not before)**:
  wp_apply-class law application, the Access-style
  whole-struct↔field bridging tactic (G-REPR's companion),
  normalization/`omega` side-condition discharge, `wp_auto`-style
  redex walking on top of the pin's ectx finder.
- **Price ([AGENT])**: probe 0.5 session; build-out honestly
  unknown until probed — reserve 1–2 sessions in phase B pricing,
  re-priced at the probe.

### 4.9 Deferred rows (named, not scheduled)

- **G-STITCH** (the `Steps`→`stepFnIter` stream-stitching converse,
  `MachineSound.lean` records it unproved): needed only if an
  ∃-shaped claim ever routes through the relation; defer until
  demanded.
- **G-CONC** (channels/select/sync at tier 3; the StepM pairing
  obstruction is recorded at `Surface.lean:591-601`): the
  channel-logic park's territory; resume conditions unchanged
  (U0 discharges condition (i)); OUT of corpus-era scope except
  that the corpus DESIGN reserves pattern-class slots for it
  (§5.4).
- **Per-type instance GENERATION** (A6 — automation at scale):
  Goose needed ~1,400 machine-generated `Access`-class instances to
  serve real codebases; our per-type points-to/value-typing
  instances (G-REPR's companions) will hit the same wall. Named
  trigger: **the raft member** — hand-written instances suffice for
  the 15–60-line corpus; the raft charter includes a small
  generator over the frontend's type table if the count-per-type
  measured on the corpus extrapolates past hand-writing.

### 4.10 Sequencing — the dependency graph (explicit)

```
      U0 (iris-lean refresh)     H + A-TRIP (early units, §6.3)
        │ (tactic base; total-WP   │ (ChoiceCanon kill, judge-parser,
        │  theory adopted)         │  fjRunDeadlocks; the veneer lint
        ├───────────┬──────────────┘  then the closure checker)
        ▼           ▼
     G-BIND      G-REPR ◄── design probe first (route (b) presumptive;
        │           │  \      sibling-frame write = the test)
        ▼           │   ►(readers re-seated; own_map/own_slice)
     G-CALLS ◄──────┤            │
        │           │            ▼
        │           │        G-MAPITER ──► G-SORT (+Sort census)
        ▼           ▼            │
   C-05/07/12   C-08 (+C-13's   C-01/02/09
                 field chain)    │
     U0 ──► G-TOTAL ──► C-15 (+C-01's Terminates form)
        └───────────┴────────────┘
                    ▼
             G-AUTO probe  (after the first 2 structural units land;
                    │       before any corpus-wave charter)
                    ▼
         corpus waves (§5, remaining cases incl. C-16..C-20)
                    │
     G-EXIT ──► C-13 initchain ──► G-STMTS drafts ([USER] designation)
                    │
                    ▼
        RAFT MEMBER: G-INV ([USER] gate) → the restored §5.3 rows
        (U3.2b/c/d/e/f, guard-silence table) → cluster FnSpecs →
        driver loop → AgreementT1/TotalT1/NeverFaults ([USER]
        designation)
```

Ordering rules: U0 strictly first (everything downstream sits on the
moved pin — building laws against the old pin buys migration debt);
G-REPR's design probe may run parallel to G-BIND (disjoint trees);
G-CALLS strictly after G-BIND; the G-AUTO probe gates the first
corpus WAVE (single cases used as unit gate instances may land
before it); G-EXIT anytime after U0 (independent of G-REPR); the
raft member strictly last, behind its two [USER] gates.

### 4.11 G-INV and G-STMTS (the raft member's own units — listed here, gated in §6)

**G-INV** — the driver-loop invariant re-designed at the Iris tier.
*Quantifier-audit line: ∀ iterations at the driver loop, by the
loop-invariant rule over the amended contract — the clause inventory
is the invariant's content, G-REPR supplies its heap half.
LINEAGE: Floyd/Hoare loop invariants; the archived clause inventory
(`archive/callspec-era`'s `Invariant.lean`, minus the two F-1-defective
clauses) is the base inventory; the v3-DRAFT §D-A designs
(concrete-log↔NH pairing + `hview`, the freshLog vote-square
sub-clause, the quiescence clause + its two reader extensions, the
Star/certified transport) are the amendment's content, re-shaped as
⌜–⌝-embedded pure clauses + G-REPR heap assertions.* First act
(A3): the mechanized logBridge/commitTie REFUTATION, kept as a
regression witness (v3 §D-A A1 — the record of why the two clauses
died). The design GATE is the [USER]'s — the re-run of W2.5 under
the post-mortem's corrective rules (§6.2, N-4): hard stop; the gate
reviews the FIRST IMPLEMENTATION built against the note, not the
note alone. Price ([AGENT], v3 anchor): ~2 sessions + the gate.

**G-STMTS** — the raft sentence drafts (`TotalT1`, `NeverFaults`
Props + the NeverFaults-from-Total corollary via
`runProgramM_classify_of_total`) + the designation act. Price: 0.5
session + the [USER] ceremony + judge.

---

## 5. The corpus design

From the triage plan §7 (the 15 pattern classes, the seed
assessment, the coverage matrix — its "≈10–14 new programs" row sums
are this section's input), extended per A3 by the census-vs-corpus
CONSTRUCT reconciliation (C-15..C-20 + written scope-outs, §5.2b).
The [USER] aim is reinstated in full: "a clean set covering ALL
patterns Raft needs **(plus explored extras)**" — the reconciliation
members and the scope-out ledger are the explored-extras clause made
concrete. Standing rules for EVERY corpus program:

- **Differential-tested Go first** (guardrails-first, charter): the
  program enters `Corpus/` as canonical Go with edge-case siblings
  and classifies correctly under `go run` differential BEFORE any
  spec work. A program the tool can't lower is visibly
  frontend-blocked, never a false pass.
- Statements per §2a (FuncSpec-analogue + readout + **negative
  twin** + totality where apt); proofs per §2b (through the WP
  calculus — the veneer test applies).
- Small on purpose: ~15–60 lines of Go each ("enough richness that
  cheating is hard, but tiny enough to motivate success" — the
  [USER] aim, verbatim).
- Sizes below are [AGENT] estimates of the Go source; the
  per-case proof cost is set by the G-AUTO probe, not guessed here.

### 5.1 The seed pool (already exists, stays)

Iris-track seeds: the golden pin, GoldenRecover, the three quorum
pilots + `committedIndexAllConfigs`, GoldenSliceWP, GooseParity
quartet, Fib, AutomationTargets — genuinely covering PC-11/12/15 and
partially PC-1/2/3/4/7/13. The 26-program gallery is
OVERWHELMINGLY stepFn-track — its large flagships (SliceQueue,
SliceStack, MatMul, Kadane, …) carry zero `WP (`; `Examples/Fib`
is the recorded exception (6 `WP (` occurrences — it is why Fib
sits in the Iris-track seed list above; A6 correction of this
draft's earlier "zero in flagships" phrasing). The gallery seeds
PATTERNS and lowered programs; re-speccing a gallery program at
tier 3 is itself corpus exercise (three cheap re-specs below).

### 5.2 The new members (each: name · ~Go size · pattern(s) · canonical properties incl. negative twin · gating unit)

| id | name | ~size | pattern(s) | canonical properties (designated set per §2a) | gates |
|---|---|---|---|---|---|
| C-01 | `mapwalk` | 25 | PC-1 (key+value range, demonic order) | sum-over-values FnSpec (order-invariant readback); Perm-of-draws readout; twin: off-by-one accumulator refuted; Terminates | **G-MAPITER gate instance** |
| C-02 | `mapmutate` | 30 | PC-1 (mutating body) | range with in-body write/delete; final-map FnSpec in lookup vocabulary; twin: stale-read variant refuted | G-MAPITER (width) |
| C-03 | `lockstat` | 25 | PC-2 (Lock/defer Unlock, plain return) | locked-read FnSpec; counter-incremented-once readout; twin: double-unlock variant is frontend/differential-refuted, spec twin refutes wrong count | **G-AUTO probe case** |
| C-04 | `lockget` | 30 | PC-2 (defer-tail WITH result — the `.next (.frame …)` arrival geometry) | (value) FnSpec through the deferred exit; twin: wrong-field read refuted | G-CALLS (geometry 2) |
| C-05 | `callchain` | 30 | nested static calls + defer (PC-15 touch) | composed FnSpec proved via `wp_bind` at open caller context; twin: swapped-callee refuted | **G-BIND gate instance** |
| C-06 | `ifacesum` | 35 | PC-4 (n-ary interface method) | dispatch FnSpec at a pinned iface field, arity ≥3; twin: wrong-method refuted | G-CALLS (width) |
| C-07 | `stepfield` | 35 | PC-5 (func-value FIELD dispatch — `r.step` in miniature) | dispatch-through-field FnSpec; both assignments of the field exercised; twin: unassigned-field variant fails closed | **G-CALLS gate instance** |
| C-08 | `protoclone` | 45 | PC-6 + PC-13 (deep-struct clone; nested field chains) | clone FnSpec: source footprint intact (frame), copy per-field-equal, ∃-address for the copy; twin: aliasing variant refuted (separation does the work) | **G-REPR gate instance** |
| C-09 | `miniids` | 40 | PC-7 + PC-1 (build map → collect keys → sort) | sorted-IDs FnSpec: result = sorted key multiset, ∀ draw orders; twin: dropped-key refuted; ALSO the owed `mapPickLoop_perm`/`MapPermRead` scaffold discharge | **G-MAPITER + G-SORT** |
| C-10 | `growstack` | 30 | PC-8 (append-capacity latitude, UNOBSERVED) | push/pop FnSpec ∀ capacity draws — this member's statements stay capacity-free (latitude quantified away); the latitude-OBSERVING sibling is C-16 (A3); twin: LIFO-order violation refuted | G-REPR (`own_slice`+cap) |
| C-11 | `pipedrain` | 45 | PC-9 (+PC-1/2 pieces: produce-then-drain queue) | drain FnSpec: emptied source, sink = produced multiset; twin: lost-message refuted | corpus width (composes 4.1–4.4) |
| C-12 | `finderr` | 35 | PC-10 (+PC-3: (T,error) return, error-global trichotomy) | three-arm FnSpec2 (ok/compacted-analogue/unavailable-analogue), error globals by identity; twin: swapped-error refuted | **G-CALLS gate instance** ((T,error)) |
| C-13 | `initchain` | 40 | PC-14 (globals + `$pkginit` + constructor cascade) + a nested-field `fieldchain` read (PC-13) | the first whole-program `runProgramM` sentence (AgreementT1 shape) + NeverFaults corollary; twin: wrong-init-order-sensitive readout refuted | **G-EXIT gate instance** |
| C-14 | `tribound` | 25 | PC-3 (data-branch trichotomy, u64 bounds — PC-11 density) | three-arm branch FnSpec with symbolic bound crossings; twin: boundary-off-by-one refuted | corpus width (crossing-kit patterns at tier 3) |
| C-15 | `countloop` | 15 | bounded while loop with a decreasing counter | `Terminates` proved SYMBOLICALLY (variant rule — no `allStreamsOk`); total readout; twin: off-by-one final value refuted | **G-TOTAL gate instance** (A1) |
| C-16 | `capcheck` | 30 | cap()-READING branch (the `shrinkEntriesArray` shape — latitude-OBSERVING control flow) | FnSpec ∀ capacity draws where the RESULT is capacity-conditioned (branch on cap); conclusion = the draw-indexed family, honestly stated; twin: branch-inverted variant refuted | corpus width; stresses G-REPR's cap carrier + G-MAPITER-era draw handling (A3) |
| C-17 | `ringbuf` | 45 | the inflights ring-buffer shape (index arithmetic over a fixed backing array, wraparound) | add/freeTo FnSpec with the ring's content abstraction; twin: lost-slot refuted | corpus width (A3) |
| C-18 | `valarray` | 40 | fixed-size arrays as VALUE types (`[2]MajorityConfig` miniature) + methods on a named map type (`map[K]struct{}` set idiom); nil-receiver note ridden here if the frontend lowers it | joint-quorum FnSpec over the two-element array value; set-method FnSpec; twin: single-half quorum refuted | corpus width; G-REPR value-type coverage (A3) |
| C-19 | `visitcb` | 40 | variadic params + function-typed parameters/callbacks (the `confchange.chain`/`tracker.Visit` shape) + a three-result return | visit-in-order FnSpec (callback contract threaded as an FnSpec premise); twin: skipped-element refuted | G-CALLS width (A3) |
| C-20 | `deadbranch` | 30 | the prove-branch-dead class (census U3) + the DEAD-NONDETERMINISM shape (census U4: a draw whose value cannot affect the observable result) | FnSpec concluding the branch is unreachable (feeds the NeverFaults idiom) + draw-irrelevance stated via footprint framing — **the natural gate instance for the [USER] footprint insight** (choices outside the footprint are frame-irrelevant, §4.2), added as such per A3 | corpus width; G-REPR footprint demonstration (A3) |

Gallery re-specs (cheap width, after the probe): **Histogram**
(PC-1), **BinSearch** (PC-3), **SliceStack** (PC-8 — may substitute
for C-10 if the re-spec is cheaper; [AGENT] call at the wave).

### 5.2b The census reconciliation and the scope-out ledger (A3)

**Gate N-3 gains a criterion**: a construct-by-construct
reconciliation of the reachability census against the corpus roster
— every census-reachable construct either has a corpus member or a
WRITTEN scope-out, signed at N-3. The reconciliation as of this
draft:

- **Members added above**: cap()-reading branches (C-16 — note this
  is why C-10's "capacity-free statement" could not stand alone:
  raft needs latitude-OBSERVING control flow), fixed-size arrays as
  value types + named-map methods + `map[K]struct{}` (C-18), the
  inflights ring buffer (C-17), variadic + function-typed params +
  three-result returns (C-19), prove-branch-dead + dead
  nondeterminism (C-20), the symbolic-Terminates loop (C-15, from
  A1).
- **Scope-outs (written, decided at N-3)**: live
  `fmt.Sprintf`/`strings.Join`/`[]byte`/`bytes.Equal` — the
  string/byte builtin family; [AGENT] proposal: a spec-vocabulary
  decision (axiomatize-as-laws vs a small member) is POSED at N-3,
  not defaulted. Nil-receiver methods — ride C-18 if the frontend
  lowers the idiom, else a written scope-out with the frontend gap
  named. The ~20-arm switch SCALE — not a member: a named G-AUTO
  probe criterion (§4.8).

Coverage check against the triage matrix: PC-1 (C-01/02/09), PC-2
(C-03/04), PC-3 (C-14 + BinSearch), PC-4 (C-06), PC-5 (C-05/07),
PC-6 (C-08), PC-7 (C-09), PC-8 (C-10/C-16/SliceStack), PC-9
(C-11), PC-10 (C-12), PC-11 (C-14/C-17 + quorum seeds), PC-12
(seeds, covered), PC-13 (C-08/C-13), PC-14 (C-13), PC-15 (seeds +
C-05) — **all 15 classes owned**, wholly-uncovered classes
(PC-5/6/8/9/10/14) each pinned by a NEW program sitting behind
exactly the structural unit the triage predicted; the A3
reconciliation members (C-15..C-20) cover the census-reachable
CONSTRUCTS the pattern classes abstracted over, with the §5.2b
ledger owning the remainder.

### 5.3 The final member: raft

The twin harness returns as corpus member C-FINAL, spec'd like every
other member — differential-anchored subject (already true),
designated sentences, negative twins per §2a, proofs through the
layer. Framing corrected per A3: the earlier draft's "the checker's
violation counters ARE the negative instrumentation" was INVERTED —
`violations = 0` is not free instrumentation but **twelve proof
obligations** (each guard's silence must be PROVED), six of them
harness-liveness guards; the guard-silence ASSIGNMENT TABLE below
owns each one. Its member spec points at:

- **G-INV** — the invariant amendment (the Elected-phase repair:
  the archived clause inventory minus `logBridge`/`commitTie`, plus
  the v3 §D-A pairing/freshLog/quiescence designs re-shaped for
  tier 3) under the **[USER]-gated W2.5 re-run** (§6.2 N-4);
- **G-STMTS** — the `AgreementT1`/`TotalT1`/`NeverFaults`
  designation (§6.2 N-5);
- the handler/library specs re-derived as tier-3 FnSpec
  postconditions (the archived member CONCLUSIONS are the harvest
  reference — `ARCHIVE.md` harvest pointers; the archive is never
  cited by a proof).

**The named phase-D rows (A3 — ownership restored; the v3-DRAFT's
priced designs are the content pointers, re-shaped for the Iris
tier at charter time; dropping these from the plan would have
dropped ownership, not work):**

| row | content (pointer) | note |
|---|---|---|
| guard-silence assignment table | each of the 12 harness guards' silences bound to an owning unit (the v3 §5 item-4 table: checker sites → the U3.2d successor; harvest/drain guards → the U3.2c measure + harvest specs; propose-stuck + quiescent-without-S4 → the U3.2e case analysis; storage-failure guards → member nil-error conclusions; unexpected-snapshot → the ProgOk/census chain) | the C-FINAL framing fix made concrete |
| U3.2b — ack evidence | ghost-acks → `certified` at commit-advance; discharges `HStep.leaderCommit`'s premise + the Star/certified transport | **the landed ghost-acks substrate's named consumer** (repairs §1's promise) |
| U3.2c — the harvest-quiescence measure | the 64-round guard silent via a lexicographic drain measure; floor = the quiescence clause; **park-not-weaken clause stands** (restored per A1 — this is G-TOTAL's raft-scale continuation and the hardest totality obligation) | v3 anchor: 1–2 sessions |
| U3.2d — checker reshape / `dataEnc` supplier | the fold-equation unit over the arc4d projections (the park's named resume); supplies the `dataEnc` joint the pairing clause needs | v3 anchor: 1–2 sessions |
| U3.2e — the driver body spec | case analysis over the invariant-constrained net population (NetCorr) at the pick; I-preservation per delivery case | v3 anchor: 2–3 sessions |
| U3.2f — raft loop-head establishment | the raft BASE CASE: newTwin/newRaft init chain establishes I at the loop head — **C-13 is a toy init and does not own this** | v3 anchor: 1–2 sessions |
| the logBridge/commitTie refutation | mechanized refutation of the two deleted clauses, kept as a regression witness (v3 §D-A A1) — G-INV's first act | small |
| the inline-threshold policy | inline remains sanctioned below a stated crossing threshold; the threshold is written at the raft charter, not re-litigated per member (v3 §D-B policy) | policy row |
| native-witnesses retirement | the two retained interface witnesses' retirement condition gets an owner at the raft charter (supersession by the tier-3 chain or an explicit keep) | ownership row |

Raft work BEGINS only after the first-checkpoint review (§6.2 N-6)
confirms the layer is real on small cases.

### 5.4 Reserved rows (not built now)

Concurrency pattern classes (channels/select/fork) get corpus SLOTS
reserved in the numbering but no programs this era — they belong to
the channel-logic resume (G-CONC), whose own gate conditions stand.
Recording this here keeps the corpus's pattern taxonomy stable when
that road opens.

---

## 6. Gates and ceremony

### 6.1 The post-mortem's corrective rules BIND this plan

Per `docs/2026-08-28_w25-gate-postmortem.md` (commissioned and
closed by the [USER] 2026-08-28):

1. **Named design gates are HARD STOPS** — no autonomous directive,
   goal monitor, or completion pressure overrides one; a run that
   cannot stop exits rather than self-adjudicating. (The charter
   amendment carrying this language is itself gate N-7 below.)
2. **A design gate reviews the first implementation built against
   the design, not the note alone.**
3. **Autonomous-goal prompts enumerate the named gates up front** so
   a stop-at-gate reads as goal-compliant. The list in §6.2 IS that
   enumeration for this plan's arcs.

### 6.2 The named [USER] gates of this plan (each a HARD STOP)

| # | gate | when | object under review |
|---|---|---|---|
| N-1 | **This plan's adjudication** | now | this document; on sign-off it becomes the plan of record |
| N-2 | **U0 execution moment** (trust-tool edge) | at unit 0's pin-move commit | the comparator/lean4export re-pin — conditions pre-approved 2026-08-20, the MOVE still requires at-the-moment approval per the trust-tools rule |
| N-3 | **Corpus-design sign-off** | before the first corpus program is built | §5's program list + per-program property sets + **the census-vs-corpus construct reconciliation (§5.2b: every census-reachable construct has a member or a written scope-out, signed here)** (the [USER] shapes the corpus; per rule 2, the first BUILT corpus case returns for a conformance look) |
| N-4 | **G-INV — the W2.5 gate re-run** | before any raft cluster work consumes the invariant | the amended design note AND the first implemented clause set built against it (rule 2 verbatim — this is the gate whose override caused the post-mortem) |
| N-5 | **Designation acts** (G-STMTS + per-corpus batches) | per corpus wave; at the raft member | the posed sentence batches; [USER]-only; judge re-run follows every designation change |
| N-6 | **The first checkpoint — "is the layer real?"** | after the first 2–3 corpus closures | the closed cases end-to-end: statement honesty, proof route (veneer test), measured throughput vs the plan's prices; the era's pricing is re-based here |
| N-7 | **The charter amendment sign-off** | at the next CLAUDE.md touch | the post-mortem's corrective-action-1 hard-stop language under "Autonomous arcs" |

### 6.3 The early units: the hygiene slice (H) + the veneer tripwire (A-TRIP) — small, first landings after N-1

The scheduled debt batch, all [USER]-ruled or audit-flagged
(campaign log 2026-08-28, the four merge rulings + deferred items):

- **`ChoiceCanon` kill** (`Frame/ChoiceCanon.lean`, 616 lines +
  its Audit pins): [USER] ruling 2026-08-28 — KILL at the next
  hygiene slice; rationale recorded in §4.2 (footprint subsumption
  under G-REPR). Archive-ref note in ARCHIVE.md; the parked SpanIso
  lane's `Mask` dependency gets a park-record note (its resume
  re-derives or harvests from the archive).
- **`Audit.lean` comment wording** (the audit's M-1 residue —
  deferred because judge-parsed region): fix the provenance wording
  in the designated-list comments; judge re-runs (this slice's
  landmark covers it).
- **Judge-wrapper parser hardening**: replace the sed extraction
  that a `[USER]`-string comment truncated (empirically reproduced,
  fail-closed, fixed comment-side at the triage) with a parse that
  is robust to comment content — our apparatus, gate-governed,
  trust-adjacent flag on the commit.
- **`fjRunDeadlocks` retirement** (`Specs/ForkJoinTargets.lean:107`
  + its two remaining non-designated pinned-stream theorems in
  `GoldenForkJoin.lean`): already de-designated at the triage;
  retire the def + theorems + pins (subsumed by the all-schedule
  family), completing the pinned-stream-row cleanup.

*Price ([AGENT]): 0.5 session + one judge landmark (batched with
U0's if the slices land together).* Trust-adjacent items ride their
own flagged commits per standing practice.

**A-TRIP — the veneer tripwire (A2; early, cheap, its own unit).**
*Quantifier-audit line: advances no quantifier — it is the
mechanized enforcement of §2d's proof-route rule. LINEAGE: the
project's own Audit closure-walker, re-aimed from statement
closures at PROOF-TERM closures.* The gap it closes
(review-verified): the Audit gate polices statement closures only
("Proofs may use anything"), and at corpus scale a span-grinding
veneer is a cost INLIER — no existing check catches it; negative
twins don't either (a veneer proves a twin as easily as the
positive). Two forms, shipped in order:

1. **Day-one text-lint** (lands with H): in designated-WP proof
   files, no `decide`+kernel closures, no direct `stepFn`/
   `stepFnIter`/`execStmt` unfolds, no `allStreamsOk` — a
   fail-closed grep-class check in `scripts/ci`, list-scoped to
   the corpus proof modules.
2. **The proof-side closure check** (the unit proper): reusing the
   existing Audit closure-walker infrastructure, walk the PROOF
   TERMS of tier-3 corpus lemmas and verify that
   `stepFn`/`execStmt`/`stepFnIter`/`allStreamsOk`/kernel-decision
   constants are reached only THROUGH the Laws/lifting/adequacy
   layer, never directly. Whitelist = the layer's module list;
   violations name the constant and the reaching path (sealed
   fail-closed reporting, per charter).

Declared carve-outs (so the check is honest, not theater): the
∃-discharge sites the charter sanctions (reflection certificates,
`InitSpec`-class setup facts) are OUTSIDE the checked set by
designation, listed in the checker's config with provenance.
*Price ([AGENT]): 0.5 session (lint ≈ hours; the walker re-aim is
the substance).* Consumers: every corpus closure review, gate N-6.

### 6.4 The standing ceremony (unchanged)

The merge protocol is UNCHANGED and applies to every arc: work on
branches in worktrees (one writer per worktree), `scripts/ci` via
`scripts/capped` before any runtime-touching commit (+ `--diff` for
runtime changes), `scripts/comparator-judge` at landmarks
(designated-statement changes, trusted-closure movement, staleness
notes), the unconditional pre-merge adversarial audit ASK (scope and
waiver are the [USER]'s; reviewers Opus, workers Fable), pause for
at-that-moment merge sign-off, ff-only merge, end parked on main,
push a separate sign-off. Autonomous arcs run inside written
boundaries with §6.2's gate list enumerated in the goal prompt.

---

## 7. Pricing and the delivery metric

All prices are [AGENT] estimates against the measured anchors
(v3-DRAFT §2: member/mechanism session costs; W2: 2,948 lines/
session probe-first; triage §5.3 per-unit signals; judge: 51
theorems / 122 s fresh-clone; gate: 460 s warm at the triage tip).
The honest caveat, stated up front: the anchors were measured on the
CallSpec-era proof style; tier-3 throughput is exactly what the
G-AUTO probe exists to measure, and N-6 re-bases everything after
the first closures.

| phase | contents | price ([AGENT]) |
|---|---|---|
| A — foundations | U0 (2–3, incl. the committed total-WP adoption) + hygiene slice H (0.5) + veneer tripwire A-TRIP (0.5) | **3–4 sessions** |
| B — the structural ladder | G-BIND (1.5–2, re-priced under A5) + G-REPR (2–4) + G-CALLS (1–2) + G-MAPITER (1) + G-EXIT (0.5–1) + G-SORT (0.5 incl. the Sort census) + G-TOTAL (1) + G-AUTO probe (0.5) | **8–12 sessions** |
| C — corpus width | the 11 remaining new cases (C-02/04/06/10/11/14/16/17/18/19/20 — a tiny-to-medium mix) + 3 gallery re-specs at probed throughput (planning figure 0.5–1 session/case until N-6 re-bases it; the tiny members expected under it) + G-AUTO build-out reserve (1–2) | **7–13 sessions** |
| D — the raft member | G-INV (≈2 + gate) + G-STMTS (0.5 + ceremony) + the restored §5.3 rows (U3.2b 0.5–1, U3.2c 1–2, U3.2d 1–2, U3.2e 2–3, U3.2f 1–2, refutation/policy rows ≈0.5 — v3 anchors) + handler-tier FnSpecs + the loop instance & total variant + seam/readout | **10–17 sessions** (LOW-confidence; the named rows now sum visibly instead of hiding in a flat band; re-priced at N-6 and again at the raft charter) |

**Era total ([AGENT], wide band, honestly): ≈ 28–46 worker-sessions**
to the raft summit sentences, with phases A+B (**11–16 sessions**)
the high-confidence prefix and N-6 the re-basing point.

**Revision-1 pricing delta, attributed (was ≈ 21–36):** +1.5–2.5
totality machinery that revision 0 wrongly assumed existed (U0's
committed adoption, G-TOTAL, U3.2c restored to the visible sum);
+0.5 A-TRIP; +0.5 G-BIND's inverse-decomposition obligation;
+2–4 the six census-reconciliation corpus members; +2–3 the restored
phase-D rows now priced explicitly rather than absorbed into a
low-confidence band. The growth is disclosure, not scope creep:
A1/A3 named work the summit always required.

Dominant named risks: (1) G-REPR's design probe forcing a redesign
loop (budgeted); (2) tier-3 throughput vs the CallSpec anchors
(probed at G-AUTO, checked at N-6); (3) the raft-member figure's
low confidence (re-priced twice before it spends); (4) U3.2c's
measure (park-not-weaken clause stands).

**The delivery metric of the era: corpus cases closed CLEANLY per
week** — "cleanly" = differential-anchored subject, designated
sentence + readout + negative twin (+ totality where apt), proof
through the WP calculus passing the veneer test, gate + (on
designation) judge green. Not lines, not laws, not members.

**The first checkpoint** = gate N-6: the first 2–3 corpus closures
reviewed by the [USER] — "is the layer real?" — before corpus-wave
throughput is claimed or the raft member is chartered.

---

## 8. Open [USER] decisions collected (beyond the §6.2 gates)

1. **This draft** (N-1): adopt as plan of record; v2 superseded with
   a banner.
2. **U0 boundary rev**: pin to upstream head at unit open vs the
   in-flight 4.33 bump line — chosen deliberately with the [USER]
   at the unit's start, per the delta scan's "pin once, don't
   chase".
3. **FnSpec notation**: adopt upstream Texan-triple/telescope
   notation for tier-3 contracts, or keep the current
   `GoFuncSpec`-shaped raw form (statement-layer sentences are
   unaffected either way — they stay Surface-shaped).
4. **C-10 vs SliceStack re-spec** ([AGENT] will propose at the
   corpus wave; flagged as a [USER]-visible swap since it changes
   the corpus roster of N-3).
5. **Designation batching cadence** (per-wave proposed; per-case if
   the [USER] prefers tighter judge coverage).
6. **The parked lanes** are untouched by this plan (channel-logic,
   arc4d, ce/SpanIso keep their named resume conditions); confirm
   no re-sequencing is wanted this era.

---

*Provenance: [AGENT]-drafted end to end from the cited sources; the
[USER] statements quoted are from the campaign log entries of
2026-08-27/28 and the 2026-08-20 delta-scan rulings. No execution
of any unit has occurred; no file outside this document was
modified by this draft.*
