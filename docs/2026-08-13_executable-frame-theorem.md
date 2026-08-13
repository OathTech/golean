# The executable frame theorem — command locality for GoCore (2026-08-13)

Status: DESIGN OF RECORD for slice 2b part 1 (ruling: route (β), user
2026-08-13). The user's framing, recorded: **this is the
COMMAND-LOCALITY property from separation logic** — the semantic fact
(Yang/O'Hearn's safety monotonicity + frame property, stated on the
EXECUTABLE machine) needed to layer even a simple SL; subtleties
expected, with addressable stack pointers named as the exemplar class.
Consumers: the ∀-frame TOTAL headline forms (fib upgrade, `reverse_ok`,
every 2b/2c example), and — cross-record, per the ruling — **the NPDRF
revival kit**: obstruction 1 of `GoLean/GoCore/NPDRF.lean`'s scaffold
status ("the reduction must be stated up to an address renaming (a heap
isomorphism)") names exactly this machinery; P-S4NP-2's heap-iso need
and this theorem's renaming are ONE artifact — whoever builds either
first hands the other its kit.

## §1 The statement (locality up to fresh-address renaming)

Setup. A canonical seed `(H₀, na₀)` (the input cells, allocator at
`na₀`, `MachineWf`-admissible) and a framed seed `(H₀ ++ fr, na)` with
`fr` disjoint from `H₀`'s addresses and `na` admissible for the
combined heap (`MachineWf` again — which forces `na` above every
address `fr` mentions, keys and pointer values both).

The renaming is the **uniform shift on run-allocated addresses**

    ρ : Nat → Nat,   ρ x = if x < na₀ then x else x - na₀ + na

— identity on every pre-existing address (so on everything `H₀`
mentions), a bijection between `[na₀, ∞)` and `[na, ∞)` (the two runs'
fresh ranges; allocation is sequential — `ExecState.freshLoc` hands out
`nextAddr` and increments — so the k-th allocation lands at `na₀ + k`
and `na + k` respectively, and the shift is exactly the allocation
bijection). `ρ` extends compositionally to `Loc` (base ids; field/index
locs rename their base), `GoValue` (through `.addr`, `.slice`/`.map`/
`.chan` base locs, arrays/structs/funcVal captures pointwise),
`HeapCell`, `LocalEnv`, `Cont`, `Config`, and the heap
(`renameHeap ρ h` renames keys and cell contents).

**The per-step simulation** (the theorem proved by induction over
`stepFn`, every arm):

    stepFn σ c ch = .ok (c', σ', ch')
    → SimState σ σF → SimConfig c cF
    → ∃ σF' cF', stepFn σF cF ch = .ok (cF', σF', ch')
        ∧ SimState σ' σF' ∧ SimConfig c' cF'

where `SimConfig c cF := cF = renameConfig ρ c`, and `SimState σ σF :=`

  * `σF.nextAddr = ρ σ.nextAddr` (with `na₀ ≤ σ.nextAddr` invariant);
  * pointwise heap correspondence:
    `∀ a, a < na₀ ∨ na₀ ≤ a → Heap.lookup σF.heap (ρ-image loc)` equals
    the renamed `Heap.lookup σ.heap loc` for every loc σ's run can
    address, AND `∀ a c, Heap.lookup fr (.base ⟨a⟩) = some c →
    Heap.lookup σF.heap (.base ⟨a⟩) = some c` (frame cells inert,
    pointwise-preserved — writes only target renamed-canonical
    addresses, which are disjoint from `fr` by construction);
  * types/functions/methods equal (never renamed — programs contain no
    address literals; `Loc` does not occur in `Stmt`/`Expr` emitted by
    the frontend — `Expr.locLit` exists in the syntax but the decoder
    never produces it, which the proof records as a per-arm exclusion:
    the `locLit` arm carries the side condition "renamed programs";
    seeds built from `fibLowered`-class programs satisfy it trivially).

Iterated (`stepFnIter`, then `execStmtLoop` — terminals correspond
because `renameConfig` preserves the nine terminal shapes), this gives
the two transfer corollaries the headlines consume:

  * **Completion transfer**: `CompletesIn f σ c → CompletesIn f σF cF`
    — the fuel-measure segments proved at the canonical placement
    transfer to EVERY admissible framed placement; `∀`-frame
    termination without re-running a single segment.
  * **Fixed-address readout transfer**: our output claims read INPUT
    addresses (below `na₀`), where `ρ` is the identity — value claims
    transfer un-renamed. Frame preservation is clause 2 of `SimState`
    at the terminal state.

Direction, stated honestly: the theorem transfers **success**
(canonical `.ok` steps to framed `.ok` steps). It does NOT claim the
converse (a framed run's behavior bounds the canonical run's) and the
headlines don't need it — see §3 wild reads for why the converse is
the delicate direction and how fail-closed reads make the success
direction the safe one.

## §2 Subtlety (a): there is no stack — verified

The classic SL stack-pointer subtlety (locals live in an environment;
`&x` forces an escape analysis or a two-sorted model) DISSOLVES in
GoCore by a modeling fact: **every local is a frame-entry heap cell.**
Verified against the machine, not asserted: declarations allocate via
`ExecState.alloc` (heap append + `nextAddr` bump — `Step.initialization`,
`bindParams`, `allocDecls`); `LocalEnv` maps names to `Loc`s — it
STORES no values; `&x` is `Expr.ref`, resolved control-side to the
existing `Loc` (`stepFn`'s `.ref` arm reads the env only). The only
other value positions in the machine are the CONFIGURATION's transient
registers (`retV` payloads, `strictK`/`rhsK`/`storeK`/`callArgsK`
value lists, defer chains and panic chains inside `Cont.frame` /
`panicking`) — none is addressable (no `Loc` points into a
configuration), and all are covered by `renameConfig`. So addressable
locals are uniform heap cells and the renaming treats them like any
allocation; no separate stack argument exists because no separate
stack exists.

## §3 Subtlety (b): why the renaming is sound — unforgeability, per-arm

The shift is sound only if no arm can OBSERVE absolute addresses.
Argued class-by-class against `stepFn` (the proof will discharge these
arm-by-arm; the classes below are the audit map):

1. **No int→ptr forging, no ptr→int leaking.** The fragment has no
   expressible conversion between integers and pointers: Go itself
   requires `unsafe.Pointer` as the intermediary, and the frontend's
   type mapping has no `unsafe.Pointer` arm (fail-closed default);
   `uintptr` maps to plain `uint64` (`NativeToIR.lean:62`) and no
   conversion arm produces it FROM a pointer. So `.addr` values are
   created only by allocation and `&`/handle construction — renaming
   reaches every one of them.
2. **Pointer equality is `Loc`-structural** (`valueEqFuel`:
   `.pointer _, .addr left, .addr right => return left == right`, plus
   the `.nil` cross arms). `ρ` lifts to an injection on `Loc`, so
   `==` is preserved both ways. Same for map keys containing pointers
   (map lookup walks `valueEq`).
3. **No pointer ordering, no hashing.** `valueLess`/`valueAtMost`/
   `valueGreater` accept int/float/string only (pointers are `stuck`,
   and a canonical `.ok` step therefore never compares pointers by
   order); `sortSlice` is int-only by construction; maps are
   assoc-array-backed — no address-dependent hash anywhere.
4. **Map iteration order** — the one address-adjacent nondeterminism —
   is CHOICE-STREAM-driven over the remaining-entries snapshot; the
   snapshot renames pointwise, the pick index is stream-data, and the
   simulation threads the SAME stream `ch` through both runs. (This is
   also why the theorem strengthens rather than perturbs the
   nondeterminism doctrine: the envelope is defined over streams, and
   the renaming is per-stream.)
5. **Error messages embed value `repr`s** (e.g. stuck messages
   interpolating operands — addresses included). Under renaming,
   error MESSAGES may differ between the two runs. The simulation
   dodges this by construction: it transfers `.ok` steps only, and
   the headline corollaries (completion + readout + frame) never
   inspect error payloads. Recorded as the reason the theorem is
   stated on success steps rather than as full result-equality — an
   honest scope restriction, not a weakening: fail-closed refusals
   remain refusals in every claim we make.
6. **`Expr.locLit`** — the one syntax node that embeds a `Loc` in a
   program. The frontend never emits it (decoder has no producer); the
   theorem carries "locLit-free program" as a side condition
   discharged by construction for every corpus-lowered program, OR the
   arm renames the literal along with the configuration (either
   closes; the side condition is the cheaper first version).

## §4 Subtlety (c): wild reads and the direction of transfer

A frame cell could, in principle, turn a canonical-run fail-closed
unallocated-read error into a framed-run success (the address happens
to exist in `fr`) — the classic locality failure mode. Two structural
facts make the SUCCESS direction immune:

* A canonical `.ok` step never wild-reads (its reads succeeded against
  the canonical heap), so the framed twin reads only renamed canonical
  addresses — never `fr`'s (disjoint by `MachineWf`-forced address
  separation: `na` sits above everything `fr` mentions, and input
  addresses are below `na₀` with `fr` disjoint from them by
  hypothesis).
* `MachineWf` (threaded through every step — the `stepFn_preserves_wf`
  sweep is the raw material, as the ruling notes) keeps every
  reachable pointer below `nextAddr`, so renamed reads stay inside the
  renamed image.

The CONVERSE direction (framed behaviors bound canonical ones) is
where wild reads bite, and no headline needs it; if the width arc ever
wants it, the additional premise is exactly "the canonical run's
address space is closed under the program's reads", which `MachineWf`
+ fail-closed loads supply — recorded, not claimed.

## §5 Proof plan and sizing (part 2 of the ruling — not attempted here)

Induction over `stepFn`, every arm, sized like the `*_wf` sweeps
(`stepFn_preserves_wf` and the MultiWfSound file are the direct
raw material and the shape template). Build order:

1. `renameLoc/renameValue/renameCell/renameEnv/renameCont/renameConfig/
   renameHeap` + the `ρ`-algebra (injectivity, identity-below-`na₀`,
   composition with `Heap.set`/`Heap.lookup`/`ExecState.alloc`) — one
   module, no Iris (`GoLean/GoCore`-adjacent proofs-side or core-side
   per the operator's call at landing; axioms target
   `[propext, Quot.sound]`, achievable — nothing classical in sight).
2. The helper commutations (`loadLoc`/`storeLoc`/`normalizeValueForTy`/
   `defaultValue`/`applyStrictOp`/`enterFrame`/… each commutes with
   renaming) — the bulk, mechanical, mirrors the wf sweep's helper
   lemmas.
3. The arm induction (`stepFn_sim`), then `stepFnIter`/`execStmtLoop`
   corollaries, then the two headline transfer corollaries (§1).
4. Consumption: `fib_total_framed` (fib_framed + completion transfer),
   `reverse_ok` ∀-frame total (with the §9e build list's slice-index
   WP laws for its value half), then 2c scale-out.

If an arm class genuinely resists, the recorded fallback is an honest
theorem-scope restriction naming the arm (per the ruling), never a
silent weakening. Expected resisters, pre-named: none structural; the
channel/sync arms are bookkeeping-heavy but address-blind (registries
key on renamed locs uniformly).

## §5b The allocation envelope (user direction 2026-08-13, recorded at landing)

The Go facts: the language promises NO address determinism — a
conforming implementation hands out whatever fresh addresses it likes,
run to run; the gc runtime additionally MOVES stacks intra-run
(transparently — unobservable without `unsafe`, which the fragment
refuses). The modeled observable surface for pointers is EQUALITY ONLY:
`valueEqFuel`'s `.addr` arm is `Loc`-structural `==`, there is no
pointer ordering or hashing (§3.3), no int↔ptr conversion (§3.1), and
the machine models no `%p`-style output observable (pointer formatting
is unsupported/fail-closed).

The DISCHARGE is this theorem re-read: `ρ` is generalized to ANY
injection with the fresh-region shift law (`ShiftSpec`; the uniform
shift is one instance, the input-permuting `swapShift` a deliberately
non-uniform witness — `Frame/AllocIndep.lean`), equality observations
are injection-invariant, and `execStmtLoop_ren` transfers a run to any
conforming relabeling at the same fuel/stream/outcome tag with
`FrameSim`-related terminals (`allocatorIndependence`, stated at the
empty frame). So the machine's sequential allocator is a QUOTIENT
REPRESENTATIVE of Go's unpromised address choices — the deterministic
`nextAddr` bump is scaffolding whose re-envelope obligation is
DISCHARGED BY THEOREM, not a fidelity claim. Latitude-inventory entry:
C11's allocation-addressing bullet, upgraded to the new
ENVELOPE-BY-QUOTIENT disposition (the first pin fully redeemed this
way — the model case for the class).

Honest scope: the quotient covers the MODELED observable fragment. Any
future observation channel that exposes addresses (modeling `%p`
output, pointer order, `unsafe` conversions, address-dependent map
iteration) RE-OPENS the pin; that condition is recorded on the
inventory entry.

## §5c THEORY CONSEQUENCES — the three dispositions for allocation
nondeterminism (options packet for the user discussion; NO decision
taken here)

The classical locality decomposition (Yang & O'Hearn, *A semantic
basis for local reasoning*, 2002; Calcagno–O'Hearn–Yang, *Local
Action and Abstract Separation Logic*, LICS 2007) validates the frame
rule from two semantic properties: **safety monotonicity** (a command
safe on a small state is safe on any extension) and the **frame
property** (any big-state execution projects to a small-state
execution leaving the frame untouched). The standard models get the
frame property *on the nose* only by making allocation
NONDETERMINISTIC (a fresh cell may land anywhere outside the domain);
with a deterministic allocator, running beside a frame visibly shifts
fresh addresses and the frame property holds only *up to a renaming of
locations* — the folklore fix is to quotient the model by location
permutation (in the relational-verification lineage: location
bijections, Banerjee–Naumann). Our machine has a deterministic
allocator by design (executability, differential comparability), so
the three available dispositions are exactly:

**Option Q — envelope-by-quotient (what this arc SHIPPED).** Keep the
sequential allocator; prove command locality up to fresh-address
renaming (`stepFn_sim`/`execStmtLoop_ren`) and allocator independence
(`allocatorIndependence`, §5b). Consequences:
- *Adequacy*: the machine stays a total executable function; headline
  theorems still read off `execStmt` runs; the frame/locality content
  lives in ONE proved theorem rather than in the semantics' shape.
  Safety monotonicity we get in the success direction (a canonical
  `.ok` run transfers framed — §4 records why the converse is the
  delicate direction and that no headline needs it).
- *Lane economics*: cheapest of the three at scale — termination
  segments and value walks are proven ONCE at the canonical placement
  (concrete addresses, `rfl`-computable) and transferred; the measured
  alternative was ~2.5 min/segment of symbolic-address simp per
  example (§9c route (α), rejected).
- *Observation-model boundary*: the quotient is sound exactly while
  the modeled pointer surface is equality-only; the boundary is now a
  RECORDED, load-bearing invariant (inventory C11's re-opening
  condition). Any address-exposing channel (`%p`, pointer order,
  `unsafe`) forces a move to Option C or a scope cut.
- *What a future SL inherits*: a frame rule validated against the
  renamed simulation — postconditions must be renaming-closed, which
  points-to-style assertions are by construction (they name addresses
  only through binders); the Iris-side `HProp` layer already
  quantifies locations existentially, so the quotient composes with
  the existing `InitialSplit`/`GoSpec` closure without re-proof. The
  renaming kit is also the NPDRF revival kit (§1) — one artifact,
  both consumers.

**Option C — Choices-site allocation (envelope exercised in the
machine).** Make `freshLoc` consume from the `Choices` stream (any
unused address), turning allocation into class-(a) ENVELOPED latitude.
Consequences:
- *Adequacy*: matches the COY model on the nose — the frame property
  holds per-stream up to equality, no quotient needed; metatheory is
  textbook.
- *Lane economics*: the expensive direction everywhere else — every
  termination segment, WP law, and example proof goes
  symbolic-in-addresses (route (α)'s cost, now mandatory, per proof
  rather than once); `CompletesIn`'s ∀-stream quantifier now also
  ranges over placements, and fuel bounds must be shown
  placement-invariant (true, but another proof dimension).
- *Differential*: NO ORACLE for the new width — `go run` cannot be
  driven to a chosen address; the whole envelope-too-wide direction
  would rest on review alone (the nondeterminism doctrine's known
  blind side, now at every allocation). The membership lane gains a
  stream dimension with nothing to validate it against.
- *What a future SL inherits*: the cleanest frame-rule story, at the
  price above; adequacy statements stop being "read the executable
  run" and become "for every address stream".

**Option P — plain pin, no theorem (the status quo ante).**
Deterministic allocator recorded as a (b) PIN with a standing
re-envelope obligation. Consequences:
- *Adequacy*: unchanged, but the frame property is FALSE on raw
  outcomes (framed runs produce differently-addressed heaps), so no
  frame rule can be validated against the machine at all; every
  ∀-frame headline stays run-conditioned (the pre-arc state of
  `fib_framed`).
- *Lane economics*: zero up-front, maximal deferral — a future SL
  layer must construct exactly this arc's renaming machinery inside
  its own adequacy proof, or axiomatize the frame rule against the
  relation (weakening the read-off-the-interpreter doctrine).
- This option is listed for completeness: the arc has already paid
  Option Q's cost, and Q strictly dominates P (P is Q minus the
  theorem).

The live question for the user is not Q-vs-P (Q shipped and P is its
strict subset) but whether any future width work should migrate
allocation toward C — the packet's recommendation-shaped observation,
made without deciding: C buys textbook metatheory that Q already
delivers at the observation boundary we actually model, and C's costs
land on the two things this project treats as load-bearing (executable
adequacy, differential grounding). The recorded re-opening condition
on Q is the tripwire that would force the C discussion.

## §6 Status

Part 1 (this design) — DONE, grounded per-arm against the machine.
Parts 2–3 — **PROVEN AND COMMITTED** (2026-08-13, `foundation-s1`):
the rename algebra + helper tower (handoff §1), the full ~200-arm
`stepFn_sim` induction (`Frame/StepSim.lean`, sorry-free at 4bc3052a),
`stepFnIter_sim`/`execStmtLoop_ren`/`completesIn_ren`
(`Frame/Transfer.lean`), the rename-identity-below-`na₀` family
(`Frame/RenameId.lean`), and the allocation-quotient corollary
(`Frame/AllocIndep.lean`, §5b). Axiom footprint: the classical trio;
`Classical.choice` inherited from core MachineSound
(`Machine.Heap.lookup_set_ne`), recorded in the Audit gates.
Part 4 consumption — `fib_total_framed` PROVEN (the ∀-frame TOTAL,
cce81c4d); the reverse exemplar + 2c scale-out continue per the
build-handoff record's §6.
