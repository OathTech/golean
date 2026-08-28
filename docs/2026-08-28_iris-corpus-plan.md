# The Iris corpus plan (2026-08-28) — the plan of record DRAFT for the corpus-first era

**STATUS: DRAFT, awaiting [USER] adjudication. Nothing below executes
before sign-off.** On adoption this document REPLACES
`docs/2026-08-27_clean-proof-plan.md` (v2) as the plan of record;
v2 is then superseded-in-place with a banner (its landed content —
the W0 reset, the substrate now on main — is history, not plan; the
raft-specific unit ladder of the v3 DRAFT is superseded in
architecture but its measured pricing is reused here, cited as such).

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
| 2 | `Machine.Step` (155 ctors) + `Steps`; nondeterminism = demonic rule multiplicity (tape stays at tier 1) | HAVE, raft-ready (zero sequential construct gaps vs the census) |
| 2→3 | `Lang.lean`: bare `Language` instance over `Step` (no evaluation-context structure — the G-BIND gap) | HAVE/partial |
| 3 | genuine iris-lean (pin `3877dbec`): gen_heap state interp (`Ghost.lean`), 8 lifting lemmas, 129 `wp_*` laws in 11 `Laws/*` files, 4 adequacy theorems (`Adequacy.lean`), `go_walk` tactic, non-vacuity witness gate | HAVE at function scale; 6 structural gaps (§4) |
| 3→1 readout | adequacy exits to `execStmt`/`stepFnIter` (`SurfaceExit.lean`), NOT yet to `runProgramM` (the G-EXIT gap); `RunGlue` + `InitSpec` are the landed halves of that last step | partial |
| statements | the 51-name designated set (`Audit.lean:290`), template = the Surface FnSpec family over real etcd raft quorum code | HAVE; the corpus extends it |
| substrate | plug family (+`PlugWitness`), crossing kit (+`CrossingWitness`), `MapPerm`/`MapPermRead`, readers (`AbsTwinCheckerRead`), ghost-acks (`NativeObligations`), `RunGlue`, `InitSpec`, archived invariant clause inventory | landed 2026-08-28, each with a named consumer unit below |

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

### 2d. The anti-cheating invariant (standing, era-wide)

- **Every corpus case ships its negative twin** (2a.3). A spec whose
  negative twin cannot be stated or proved is not accepted as a
  closure.
- **Proofs go through the WP calculus.** The corpus exists to
  exercise tier 3. A proof that drops through adequacy to grind
  kernel spans of the concrete run is a VENEER — it re-imports the
  banned concrete-walking method under an Iris wrapper — and fails
  review. The G-AUTO probe measures this structurally: per-case
  proof texts are expected at the Surface-family scale, and walls
  are compared against the archived CallSpec-era datum (§4.7); a
  "WP proof" whose cost profile matches kernel span-grinding is
  treated as one.
- **Bounded techniques stay banned** (charter): no fixture-anchored
  statements, no enumeration-as-∀; program-text shape constants in
  ∀-quantified rules remain the recorded carve-out.
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
| ∃ fuel (totality) | `ProgressExec`/`Terminates` + variant; classification glue | HAVE (RunGlue) + per-case |
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
  (`HeapLang/Tactic.lean`) — the direct structural template for
  G-BIND and G-AUTO.

The pin's real gaps: no telescopes → no Texan-triple notation; only
`wp_bind`/`wp_pure(s)`/`wp_rec`-class tactics (heap-step lemmas are
`iapply`-by-hand); `TotalWp` is a class with no theory behind it.

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
| `TotalWeakestPre`/`TotalAdequacy`/`TotalLifting` | the Terminates/TotalReadout family gets an upstream home instead of our lone `Specs/TotalPins` carry |
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

**Price ([AGENT]): 1.5–2.5 sessions** (pin move + toolchain as one
gated commit ≈ 0.5–1; the instance-priority tail across the 240
transitive files ≈ 0.5–1; the reuse-adoption slice (modality
instances wired into `go_walk`, TotalWp adoption assessment) ≈ 0.5)
+ the judge landmark re-run. Deliverables: the moved pin green in
its own commit; the reuse table promoted from draft with a reason on
every keep-ours row; the comparator re-pin executed under its
conditions.

**Consumers: every unit in §4** (G-AUTO most directly), plus the
channel-logic resume's named condition (i) — this unit discharges it
for that later road too.

---

## 4. The structural ladder

One unit per gap from the triage plan's §5.3 gap table, each priced
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
- **Obligation shape**: transport the `stepFn_plug` commutation to
  `Step` (case-transport, not re-derivation — `MachineSound.lean`'s
  arms mirror `Step`'s constructors 1:1 and share premise functions
  verbatim), then either (a) instantiate the pin's `Context K` class
  at `fun c => plugC env' k' c` under the two plug premises and
  inherit `wp_bind` from the library, or (b) state the direct
  bind lemma `WP c {{ _, WP plug-continuation }} ⊢ WP (plugC … c)`.
  [AGENT] recommendation: probe (a) first — inheriting the library's
  `wp_bind` is the lineage-clean route; (b) is the fallback if the
  premise-conditioned fill fights the class. Retire/absorb the
  per-arity widening-owed notes as corollaries.
- **Gate instance**: corpus case **C-05 `callchain`** (§5) — a
  nested static call with a defer, proved once through `wp_bind`
  at an open caller context (also discharges `PlugWitness`'s
  recorded retirement condition and replaces the killed W2Gate
  composition demo, closing that accepted gap).
- **Consumers**: G-CALLS (kills the per-geometry surface), every
  corpus case with a call (all of them), the raft member.
- **Price ([AGENT], W2 anchor)**: 1–1.5 sessions, probe-first.

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
  before the walk is paid): either
  (a) **view route** — keep the base-cell gen_heap and DEFINE typed/
  per-field points-to as predicates over the cell (a fraction-
  carrying lens view; the Perennial pattern transplanted to a
  cell-structured heap), with get/set access lemmas and the
  split/combine algebra; or
  (b) **re-key route** — re-key the ghost heap at (base, path) so
  per-field points-to IS a gen_heap points-to.
  Both keep tier 1/2 untouched (the assertion layer is ghost-side).
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
  per-field vocabulary.
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

Gate instance: **C-09 `miniids`** (shared with G-MAPITER — build
map → collect → sort). Price ([AGENT]): days, after G-MAPITER.

### 4.7 G-AUTO — the automation probe and build-out (the throughput referee + the veneer test)

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
  (C-03 `lockstat`) with the post-U0 tactic base; measure walls and
  proof-text size; compare against the archived CallSpec datum
  (30–60 min straight / 1–2.5 h crossing members; 11 members per
  session) — the layer must beat or match the dead calculus's
  measured throughput at equal honesty, or the build-out backlog
  reorders before cluster spends. **This is also the veneer test's
  instrument** (§2d): the probe pins what an honest WP proof costs,
  so a span-grinding veneer shows up as a cost-profile outlier.
- **Build-out backlog (sized by the probe, not before)**:
  wp_apply-class law application, the Access-style
  whole-struct↔field bridging tactic (G-REPR's companion),
  normalization/`omega` side-condition discharge, `wp_auto`-style
  redex walking on top of the pin's ectx finder.
- **Price ([AGENT])**: probe 0.5 session; build-out honestly
  unknown until probed — reserve 1–2 sessions in phase B pricing,
  re-priced at the probe.

### 4.8 Deferred rows (named, not scheduled)

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

### 4.9 Sequencing — the dependency graph (explicit)

```
      U0 (iris-lean refresh)         H (hygiene slice, §6.3)
        │  (tactic base, TotalWp)      │ (ChoiceCanon kill, judge-parser, …)
        ├────────────┬─────────────────┘
        ▼            ▼
     G-BIND       G-REPR  ◄─── design probe first (route (a)/(b))
        │            │  \
        ▼            │   ►(readers re-seated; own_map/own_slice)
     G-CALLS ◄───────┤            │
        │            │            ▼
        │            │        G-MAPITER ──► G-SORT
        ▼            ▼            │
   C-05/07/12    C-08 (+C-13's   C-01/02/09
                  field chain)
        └────────────┴────────────┘
                     ▼
              G-AUTO probe  (after the first 2 structural units land;
                     │       before any corpus-wave charter)
                     ▼
          corpus waves (§5, remaining cases)
                     │
     G-EXIT ──► C-13 initchain ──► G-STMTS drafts ([USER] designation)
                     │
                     ▼
        RAFT MEMBER: G-INV ([USER] gate) → cluster FnSpecs →
        driver loop → AgreementT1/TotalT1/NeverFaults ([USER] designation)
```

Ordering rules: U0 strictly first (everything downstream sits on the
moved pin — building laws against the old pin buys migration debt);
G-REPR's design probe may run parallel to G-BIND (disjoint trees);
G-CALLS strictly after G-BIND; the G-AUTO probe gates the first
corpus WAVE (single cases used as unit gate instances may land
before it); G-EXIT anytime after U0 (independent of G-REPR); the
raft member strictly last, behind its two [USER] gates.

### 4.10 G-INV and G-STMTS (the raft member's own units — listed here, gated in §6)

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
⌜–⌝-embedded pure clauses + G-REPR heap assertions.* The design
GATE is the [USER]'s — the re-run of W2.5 under the post-mortem's
corrective rules (§6.2, N-4): hard stop; the gate reviews the FIRST
IMPLEMENTATION built against the note, not the note alone. Price
([AGENT], v3 anchor): ~2 sessions + the gate.

**G-STMTS** — the raft sentence drafts (`TotalT1`, `NeverFaults`
Props + the NeverFaults-from-Total corollary via
`runProgramM_classify_of_total`) + the designation act. Price: 0.5
session + the [USER] ceremony + judge.

---

## 5. The corpus design

From the triage plan §7 (the 15 pattern classes, the seed
assessment, the coverage matrix — its "≈10–14 new programs" row sums
are this section's input). Standing rules for EVERY corpus program:

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
partially PC-1/2/3/4/7/13. The 26-program gallery is stepFn-track
(zero `WP (` in its flagships) — it seeds PATTERNS and lowered
programs; re-speccing a gallery program at tier 3 is itself corpus
exercise (three cheap re-specs below).

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
| C-10 | `growstack` | 30 | PC-8 (append-capacity latitude) | push/pop FnSpec ∀ capacity draws (cap never in the statement); twin: LIFO-order violation refuted | G-REPR (`own_slice`+cap) |
| C-11 | `pipedrain` | 45 | PC-9 (+PC-1/2 pieces: produce-then-drain queue) | drain FnSpec: emptied source, sink = produced multiset; twin: lost-message refuted | corpus width (composes 4.1–4.4) |
| C-12 | `finderr` | 35 | PC-10 (+PC-3: (T,error) return, error-global trichotomy) | three-arm FnSpec2 (ok/compacted-analogue/unavailable-analogue), error globals by identity; twin: swapped-error refuted | **G-CALLS gate instance** ((T,error)) |
| C-13 | `initchain` | 40 | PC-14 (globals + `$pkginit` + constructor cascade) + a nested-field `fieldchain` read (PC-13) | the first whole-program `runProgramM` sentence (AgreementT1 shape) + NeverFaults corollary; twin: wrong-init-order-sensitive readout refuted | **G-EXIT gate instance** |
| C-14 | `tribound` | 25 | PC-3 (data-branch trichotomy, u64 bounds — PC-11 density) | three-arm branch FnSpec with symbolic bound crossings; twin: boundary-off-by-one refuted | corpus width (crossing-kit patterns at tier 3) |

Gallery re-specs (cheap width, after the probe): **Histogram**
(PC-1), **BinSearch** (PC-3), **SliceStack** (PC-8 — may substitute
for C-10 if the re-spec is cheaper; [AGENT] call at the wave).

Coverage check against the triage matrix: PC-1 (C-01/02/09), PC-2
(C-03/04), PC-3 (C-14 + BinSearch), PC-4 (C-06), PC-5 (C-05/07),
PC-6 (C-08), PC-7 (C-09), PC-8 (C-10/SliceStack), PC-9 (C-11),
PC-10 (C-12), PC-11 (C-14 + quorum seeds), PC-12 (seeds, covered),
PC-13 (C-08/C-13), PC-14 (C-13), PC-15 (seeds + C-05) — **all 15
classes owned**, wholly-uncovered classes (PC-5/6/8/9/10/14) each
pinned by a NEW program sitting behind exactly the structural unit
the triage predicted.

### 5.3 The final member: raft

The twin harness returns as corpus member C-FINAL, spec'd like every
other member — differential-anchored subject (already true),
designated sentences, negative content (the checker's violation
counters ARE the negative instrumentation), proofs through the
layer. Its member spec points at:

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
| N-3 | **Corpus-design sign-off** | before the first corpus program is built | §5's program list + per-program property sets (the [USER] shapes the corpus; per rule 2, the first BUILT corpus case returns for a conformance look) |
| N-4 | **G-INV — the W2.5 gate re-run** | before any raft cluster work consumes the invariant | the amended design note AND the first implemented clause set built against it (rule 2 verbatim — this is the gate whose override caused the post-mortem) |
| N-5 | **Designation acts** (G-STMTS + per-corpus batches) | per corpus wave; at the raft member | the posed sentence batches; [USER]-only; judge re-run follows every designation change |
| N-6 | **The first checkpoint — "is the layer real?"** | after the first 2–3 corpus closures | the closed cases end-to-end: statement honesty, proof route (veneer test), measured throughput vs the plan's prices; the era's pricing is re-based here |
| N-7 | **The charter amendment sign-off** | at the next CLAUDE.md touch | the post-mortem's corrective-action-1 hard-stop language under "Autonomous arcs" |

### 6.3 The hygiene slice (early unit H — small, first landing after N-1)

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
| A — foundations | U0 (1.5–2.5) + hygiene slice H (0.5) | **2–3 sessions** |
| B — the structural ladder | G-BIND (1–1.5) + G-REPR (2–4) + G-CALLS (1–2) + G-MAPITER (1) + G-EXIT (0.5–1) + G-SORT (days) + G-AUTO probe (0.5) | **6–10 sessions** (the triage's headline, decomposed) |
| C — corpus width | the 6 remaining new cases (C-02/04/06/10/11/14) + 3 gallery re-specs at probed throughput (planning figure 0.5–1 session/case until N-6 re-bases it) + G-AUTO build-out reserve (1–2) | **5–9 sessions** |
| D — the raft member | G-INV (≈2 + gate) + G-STMTS (0.5 + ceremony) + handler-tier FnSpecs + driver body + loop instance + summit readout | **8–14 sessions** (LOW-confidence: derived from v3's 20–28-session raft ladder minus the substrate/structural work now in phases A–C; re-priced at N-6 and again at the raft member's charter) |

**Era total ([AGENT], wide band, honestly): ≈ 21–36 worker-sessions**
to the raft summit sentences, with phases A+B (**8–13 sessions**)
being the high-confidence prefix and N-6 the re-basing point.
Dominant named risks: (1) G-REPR's design probe forcing a redesign
loop (budgeted); (2) tier-3 throughput vs the CallSpec anchors
(probed at G-AUTO, checked at N-6); (3) the raft-member figure's
low confidence (re-priced twice before it spends).

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
