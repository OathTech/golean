# Concurrency research: the Iris ecosystem beyond Goose/Perennial

Worker draft, 2026-08-06. Charter: heap_lang baseline, Actris, logical atomicity,
other Iris projects' concurrency lessons, the iris-lean reality check, and
statement-idiom transfer under GoLean's Iris-internal-only constraint.

Conventions: **[FACT]** is grounded to `file:line@rev` (iris-lean checkout
`deps/iris-lean` at pinned rev `3877dbec`, verified = manifest `inputRev` in
`proofs/lake-manifest.json` and `.git/HEAD`; GoLean worktree at `a38e086`), to a
URL fetched/searched this session, or to a paper citation. Paper citations not
re-fetched this session are tagged **[FACT, from-memory citation]** — titles/venues
I am confident of but did not re-verify. **[ANALYSIS]** is my inference.

---

## 1. The heap_lang baseline

### 1.1 Concurrency primitives and semantics shape

**[FACT]** Iris's canonical heap_lang (both the Rocq original and the Lean port we
depend on) has exactly these concurrency-relevant primitives: `fork`, `cmpXchg`,
`xchg`, `faa`, plus prophecy operations `newProph`/`resolve`. No native channels,
no join, no locks — everything else is a library. Lean port:
`deps/iris-lean/Iris/Iris/HeapLang/Syntax.lean:124-135@3877dbec` (heap ops,
`| fork (e : Exp)` at 132, `| newProph`, `| resolve` at 134-135).

**[FACT]** The semantics factors into a *per-thread* primitive step and a
*thread-pool* step:

- Per-thread: `BaseStep : Exp → State → List Observation → Exp → State → List Exp → Prop`
  (`HeapLang/Semantics.lean:128@3877dbec`) — one thread's expression steps against
  the shared state, emitting observations and a list of *forked* expressions.
  `forkS` (Semantics.lean:191-192) reduces `fork e` to `unit` with forked list `[e]`.
- Thread-pool: the language-generic `Language.Step` — pick thread `i`
  nondeterministically, step it, append its forked threads at the end of the pool:
  `Step (t₁ ++ e :: t₂, σ) obs (t₁ ++ e' :: t₂ ++ eₜ, σ')`
  (`ProgramLogic/Language.lean:114-116@3877dbec`). Interleaving is *whole primitive
  steps*: physical atomicity of a primitive step is exactly "one `primStep` is one
  interleaving unit".

**[FACT]** `State` is `{heap : ExtTreeMap Loc (Option Val), usedProphId : ExtTreeSet ProphId}`
(Semantics.lean:85-88); `Observation = ProphId × (Val × Val)` (Semantics.lean:91).
`cmpXchgS` (178-185) and `faaS` (186-190) are single `BaseStep`s — CAS and
fetch-and-add are physically atomic by construction, with a `compareSafe`
(unboxed-comparison) side condition on CAS.

**[FACT]** On top of physical atomicity there is a *logical* `Atomic` typeclass
(`Language.lean:234-240@3877dbec`): an expression is (weakly/strongly) atomic if
after one primStep it is irreducible / a value. This is what licenses opening an
invariant around a single step (`wp_atomic`, used in `Spawn.lean:104,129`).
Instances for load/store/xchg/faa/cmpXchg/fork/newProph:
`HeapLang/Instances.lean:196-226@3877dbec`.

### 1.2 How channels are encoded over heap_lang

**[FACT]** heap_lang has no channel primitive; the standard channel over heap_lang
in the literature is Actris's: a **bidirectional channel = two mutable buffers
(linked lists) plus one lock**; `send` acquires the lock and enqueues on its side's
buffer; `recv` acquires the lock, dequeues from the other side's buffer, and
spin-retries if empty. Endpoints are the same triple with the buffer roles swapped.
(Actris, POPL 2020, paper PDF fetched this session:
https://iris-project.org/pdfs/2020-popl-actris-final.pdf — the fetch summary is
model-reconstructed; the two-buffers+lock structure is [FACT, from-memory citation]
of the paper and the artifact `theories/channel/channel.v` at
https://gitlab.mpi-sws.org/iris/actris.)

**[ANALYSIS]** Note what this means: in the entire mainline Iris ecosystem
(Perennial's Go channel model aside — sibling worker's charter), channels are
*programs*, not semantics. Every channel spec in this literature is therefore a
derived library spec over lock/CAS/heap reasoning. GoLean's position is the
opposite: Go channels will be *machine primitives* of GoCore with their own
envelope. That inversion simplifies nearly everything below (see §6).

### 1.3 The standard spawn/join library spec shape

**[FACT]** The canonical spawn/join (Rocq `iris/heap_lang/lib/spawn.v`, ported at
`HeapLang/Lib/Spawn.lean@3877dbec`):

- Code: `spawn f = let c = ref None; fork (c ← Some (f ())); c` and `join` spins
  on `!c` (Spawn.lean:22-32).
- Ghost structure: an *exclusive token* `γ` plus an invariant
  `spawnInv γ l Ψ = ∃ lv, l ↦ lv ∗ (lv = None ∨ ∃ w, lv = Some w ∗ (Ψ w ∨ token γ))`
  and `joinHandle l Ψ = ∃ γ, token γ ∗ inv N (spawnInv γ l Ψ)` (Spawn.lean:40-46).
  The token makes `Ψ w` claimable exactly once by the joiner.
- Specs (CPS form, Spawn.lean:69-73, 118-122):
  `spawn_spec : WP (f ()) {{ Ψ }} -∗ (∀ l, joinHandle l Ψ -∗ Φ l) -∗ WP (spawn f) {{ Φ }}`,
  `join_spec : joinHandle l Ψ -∗ (∀ v, Ψ v -∗ Φ v) -∗ WP (join l) {{ Φ }}`.
- `par` (`e1 ‖ e2`) is sugar over spawn/join with
  `wp_par : WP e1 {{Ψ1}} -∗ WP e2 {{Ψ2}} -∗ (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)) -∗ WP (e1 ‖ e2) {{Φ}}`
  (`HeapLang/Lib/Par.lean:23-70@3877dbec`).

**[FACT]** The WP `fork` rule itself: `wp_fork` at
`HeapLang/PrimitiveLaws.lean:120@3877dbec`; the forked thread's obligation is the
instance-chosen `forkPost` (heap_lang picks `True`, PrimitiveLaws.lean:38), and
the generic WP threads `[∗list] e' ∈ eₜ, wp ⊤ e' forkPost` through every step
(`ProgramLogic/WeakestPre.lean:79@3877dbec`).

**[ANALYSIS]** Lesson for GoLean's `go` statement: the fork rule is nearly free
once the machine's step relation emits forked configurations in the `primStep`
shape; the interesting design choice is `forkPost` (Go goroutines return nothing;
`forkPost = True` is right, mirroring heap_lang) and whether goroutine-local
control state (defer stack) complicates "a forked goroutine is a fresh Config".

---

## 2. Actris: dependent separation protocols

**[FACT]** Actris 1.0: Hinrichsen, Bengtson, Krebbers, "Actris: Session-Type Based
Reasoning in Separation Logic", POPL 2020 (https://dl.acm.org/doi/10.1145/3371074,
PDF https://iris-project.org/pdfs/2020-popl-actris-final.pdf). Actris 2.0:
"Actris 2.0: Asynchronous Session-Type Based Reasoning in Separation Logic",
LMCS 2022 (arXiv https://arxiv.org/pdf/2010.15030). Coq artifact:
https://gitlab.mpi-sws.org/iris/actris. Follow-ups: "Machine-Checked Semantic
Session Typing" (CPP 2021, distinguished paper), "Verifying Reliable Network
Components in a Distributed Separation Logic with Dependent Separation Protocols"
(ICFP 2023). (All URLs from this session's search.)

**[FACT, from-memory citation, structure]** The spec idiom — *dependent separation
protocols*:

- Protocols: `prot ::= ! x⃗ <v> {P}. prot | ? x⃗ <v> {P}. prot | end` — "send a value
  of shape `v` (binders `x⃗` scope over `v`, `P`, and the tail), giving up resources
  `P`" / dually for receive. Protocols are higher-order: `P` is any iProp, `v` any
  value (closures, locations, other channel endpoints — delegation).
- Ownership: a single non-persistent assertion `c ↣ prot` per endpoint. `new_chan`
  produces `c ↣ prot ∗ c' ↣ dual(prot)`.
- Specs: `{c ↣ !x⃗<v>{P}.prot ∗ P[t⃗/x⃗]} send c (v[t⃗/x⃗]) {c ↣ prot[t⃗/x⃗]}` and
  `{c ↣ ?x⃗<v>{P}.prot} recv c {w. ∃t⃗, w = v[t⃗/x⃗] ∗ P[t⃗/x⃗] ∗ c ↣ prot[t⃗/x⃗]}`.
  Client proofs are almost sequential: each send/recv peels one protocol step.
- Recursion (`μ`-protocols) gives loops and *history-tracking* protocols (the tail
  can depend on all previously exchanged binders).
- Actris 2.0 adds the **subprotocol relation `⊑`** (session subtyping as a
  logic-level judgment): payload weakening/strengthening, and crucially
  *asynchronous swapping* — receive-then-send may be replaced by send-then-receive
  — validating the reorderings sound for buffered (asynchronous) channels.
  `c ↣ prot` is closed under `⊑`.
- Model: protocols form a recursive domain (`iProto`, solved via the
  America–Rutten COFE solver, since payloads are iProps — recursion through the
  logic); `c ↣ prot` is ghost state (auth pair of endpoint protocol states) tied
  to the physical buffers by a channel invariant; the whole thing is a derived
  construction inside Iris — **no new logic, no new adequacy**.

**[ANALYSIS] Is this the state of the art for channel specs?** For *usability* on
session-shaped client code, yes — Actris remains the reference idiom (its
descendants — Multris/multiparty OOPSLA 2024, LinearActris POPL 2024, Mixtris —
extend rather than replace it; §4.8). Its sweet spot is exactly raft-relevant
traffic: request/response with resource transfer, delegation, per-channel
histories. Its known limits: (a) one `↣` per endpoint — sharing an endpoint among
goroutines needs a lock or escrow on top; (b) it is a *protocol* discipline, not
a *concurrent-object* spec — clients racing on the same endpoint (common in Go:
N workers receiving from one channel) fall outside the pure idiom; (c) Go's
`close` + zero-value receive + comma-ok has no direct Actris analogue (`end`
just stops; Go close broadcasts).

**[ANALYSIS] Could a protocol layer sit above our interpreter-level statements as
internal machinery?** Yes, structurally: Actris is fully derived inside Iris, so a
GoCore analogue would be ghost state + an invariant per channel *around our
primitive channel steps* instead of around a buffer implementation — strictly
easier than Actris's own model (no lock, no linked-list representation predicate;
the "buffer" is literally the channel queue in `ExecState`). The deletion test is
unaffected as long as `↣` never appears in an end statement (§6). The cost is the
`iProto` recursive-domain machinery; iris-lean has the COFE solver
(`Iris/Algebra/COFESolver.lean@3877dbec` exists [FACT]) but no iProto — a real
port, the single biggest optional item in §5.3.

---

## 3. Logically atomic specs and prophecy

**[FACT, from-memory citation]** Lineage: TaDA's logically atomic triples
(da Rocha Pinto, Dinsdale-Young, Gardner, ECOOP 2014); Iris's rendering
`⟨x. α x⟩ e ⟨v. β x v⟩` defined via **atomic updates** `AU` (greatest fixpoint of
an abort/commit accessor), Iris JFP 2018 + the `iris/examples` `logatom`
directory (elimination stack, conditional increment, RDCSS, Herlihy–Wing queue).
Meaning: a *non-atomic* program `e` has a linearization point at which it
atomically transforms abstract state `α` into `β`; clients may open invariants
around the whole call as if it were one instruction.

**[FACT, from-memory citation]** Prophecy variables: Jung, Lepigre,
Parthasarathy, Rapoport, Timany, Dreyer, Kaddar, "The Future is Ours: Prophecy
Variables in Separation Logic", POPL 2020. They exist precisely for
*future-dependent linearization points* (RDCSS, Herlihy–Wing queue): the proof
must decide *now* which abstract transition happened, but the answer is
determined by a later physical step; a prophecy lets the proof case-split on the
future resolution. The mechanism is operational: `newProph`/`resolve` primitives
+ observations `κs` threaded through the semantics — exactly the shape present in
iris-lean (§1.1, plus the ghost side in `BI/Lib/ProphMap.lean@3877dbec` [FACT]).

**[ANALYSIS] Channel send/recv, logically-atomic vs protocol-style.** For a
channel *implemented over finer primitives*:

- Logically atomic: `⟨q. isChan c q⟩ send c v ⟨isChan c (q ++ [v])⟩` (blocking
  makes the real statements messier: an unbuffered send has no self-contained
  atomic postcondition — the rendezvous is a two-sided commit). Strongest for
  racing clients; painful for session-shaped code.
- Protocol-style (Actris): hides the queue entirely; best for session-shaped
  code; weak for racing clients.

For GoLean the dichotomy mostly dissolves: **channel operations are single
machine steps, so "logically atomic" collapses to physically atomic** — the plain
WP lifting lemma for the machine's send/recv step *is* the atomic spec; `AU`
machinery is not needed to state or prove it. [ANALYSIS] Genuine logical
atomicity (hence an atomic-update port, absent from iris-lean — §5.3) is needed
only to verify *Go-source-level* sync objects built from finer primitives (a
mutex from CAS, a channel reimplemented in Go). Defer.

**[ANALYSIS] Will our select need prophecies?** At the semantics/laws level, no:
in GoCore, `select`'s choice is resolved at its own choice-consumption step
(nondeterminism-envelope doctrine), so the linearization point is that step —
present-determined, prophecy-free. Prophecies would enter only if (a) we exported
logically-atomic client specs for an object whose commit point is decided by a
*later* competitor step (RDCSS-class), or (b) we proved refinement against a
coarser model where select's choice must be pre-announced. Verdict: design so
prophecies stay available (iris-lean already threads observations through WP and
has ProphMap), but spend no arc budget on them.

---

## 4. Other Iris projects — one lesson each

### 4.1 RustBelt / λ-Rust

**[FACT, from-memory citation]** Jung, Jourdan, Krebbers, Dreyer, POPL 2018.
λ-Rust has fork-based concurrency and SC atomics (heap_lang-like); no channels in
the language — mpsc-style libraries are verified as unsafe-code implementations
satisfying semantic interface contracts. **Load-bearing lesson:** data-race
freedom is not assumed, it *falls out of ownership* — conflicting accesses would
require duplicating non-duplicable ownership. [ANALYSIS] For GoLean's DRF-SC
posture this is the model: "this program is DRF" is an ownership-discipline
theorem discharged by the same separation-logic proof that establishes the
pre/post — not a separate race analysis.

### 4.2 ReLoC

**[FACT, from-memory citation]** Frumin, Krebbers, Birkedal, LICS 2018; "ReLoC
Reloaded", LMCS 17(3) 2021. A refinement judgment `Δ ⊨ e ≼ e' : τ` *internal to
Iris* (WP of the left program + ghost ownership of the right program's
configuration — `spec_ctx`, thread-pointers), symbolic execution on both sides;
adequacy extracts contextual refinement. **Load-bearing lesson for our
relation-vs-interpreter correspondence:** holding *the other semantics as ghost
state* is how one proves, inside Iris, that the Prop-level relation simulates the
executable interpreter under concurrency. [ANALYSIS] But ReLoC's adequacy is
safety-flavored (termination-insensitive); if sequential conservation must
preserve termination, ReLoC's shape is insufficient — Simuliris's is the right
one.

### 4.3 Simuliris — directly relevant to fairness + sequential conservation

**[FACT]** Gäher, Sammler, Spies, Jung, Dang, Krebbers, Kang, Dreyer, POPL 2022
(https://dl.acm.org/doi/10.1145/3498689,
https://iris-project.org/pdfs/2022-popl-simuliris.pdf). Verified this session:

- The simulation is **fair termination-preserving**: if the *target* has a fair
  diverging execution then so does the *source* — equivalently, if every fair
  source execution terminates, every fair target execution terminates.
- Fairness notion: **fair thread scheduling** — in an infinite execution, every
  continuously-enabled thread eventually steps. No other liveness.
- The framework *cannot exploit* fairness assumptions on the left program, and
  supports no liveness beyond termination/divergence.
- Built on a **non-step-indexed** variant of Iris: step-indexing was dropped
  because a ▷-based simulation cannot do coinduction on divergence cleanly. They
  provide a parametric coinduction principle, hidden stuttering bookkeeping, and
  thread-local proofs lifted to whole-pool fair simulation by a framework
  theorem.

**[ANALYSIS] Transfer to GoLean's fairness quantifier + sequential-conservation
theorem.** (a) Adopt their fairness *definition*: quantify over schedules
(infinite sequences of goroutine choices); fair = every perpetually-runnable
goroutine is scheduled infinitely often. First-order over our `Step` traces —
statable in the TCB with zero Iris. (b) Their headline shape ("every fair
execution of the fine-grained program is matched, termination-preservingly, by
the coarse one") is structurally our sequential-conservation theorem. (c) The
cautionary finding: if that theorem must be *termination-preserving*, iris-lean's
step-indexed WP is the wrong proof vehicle — Simuliris exists precisely because
▷-logics can't prove it. A safety-only conservation statement can be a plain
Prop-level simulation by induction on steps (no Iris); recommend that, with
Simuliris recorded as the escalation path.

### 4.4 iGPS / iRC11 / Cosmo — weak memory (contrast for DRF-SC)

**[FACT, from-memory citation]** iGPS: Kaiser, Dang, Dreyer, Lahav, Vafeiadis,
ECOOP 2017 (release-acquire fragment in Iris). iRC11: Dang, Jourdan, Jung,
Dreyer, "RustBelt Meets Relaxed Memory", POPL 2020. **[FACT]** Cosmo: Mével,
Jourdan, Pottier, ICFP 2020 (https://dl.acm.org/doi/10.1145/3408978,
https://iris-project.org/pdfs/2020-icfp-cosmo-final.pdf; verified this session).
Cosmo instantiates Iris with the Multicore-OCaml memory model's operational
semantics (Dolan et al. 2018), then layers a high-level logic whose assertions
carry *views*: nonatomic locations get plain `↦` usable only data-race-freely;
atomics give SC-like and release/acquire rules. Verified this session: lock
implementations meet a *memory-model-independent* spec, so coarse-grained
lock-synchronized clients verify in the plain CSL fragment with no knowledge of
the weak model.

**[ANALYSIS] What Cosmo teaches about DRF-SC-only claims:** the layering works
because the model guarantees local DRF; the practical upshot is that the
high-level interface is the whole user experience and the weak model is
quarantined beneath it. GoLean taking DRF-SC as the *semantic envelope* is the
same move one level down: the interface lives in the semantics (interleaving of
primitive steps + a DRF condition) instead of in the logic. The honest-claim
obligation Cosmo highlights: a DRF-SC semantics makes *no claim at all* about
racy programs — so fail-closed requires racy executions to be *visibly outside
the envelope* (detectable-race ⇒ explicit classification or an explicit DRF
hypothesis in every theorem), never silently interleaved as if SC were true. Go's
own memory model (the 2022 Go 1.19 revision) promises DRF-SC with bounded
catch-fire, which is what makes the envelope defensible; the
nondeterminism-doctrine too-wide/too-narrow review lane applies to the race
envelope itself.

### 4.5 Iris-Wasm

**[FACT, from-memory citation]** Rao, Georges, Legoupil, Watt, Pichon-Pharabod,
Gardner, Birkedal, PLDI 2023 (follow-up Iris-WasmFX for stack switching:
https://dl.acm.org/doi/10.1145/3808271, search hit this session). Sequential; the
lesson is not concurrency but **instantiating Iris over a large, spec-faithful
operational semantics** (the official-spec-shaped Wasm semantics, not an
idealized core) and exporting robust-safety theorems in operational terms.
[ANALYSIS] Direct precedent for GoLean's architecture: an Iris WP over a big
executable semantics is a proven pattern; statements stay operational, Iris stays
machinery.

### 4.6 Osiris (OCaml)

**[FACT]** Seassau, Yoon, Madiot, Pottier, "Formal Semantics & Program Logics for
a Fragment of OCaml" (Osiris), ICFP 2025
(https://iris-project.org/pdfs/2025-icfp-osiris.pdf); earlier OCaml'23 workshop
talk. Verified this session: sequential OLang fragment (functions, ADTs,
pattern-matching, references, exceptions, effect handlers); the semantics is a
*monadic definitional interpreter* (operation-tree monad) equipped with a
small-step semantics; two logics on top (pure Hoare + Iris SL); concurrency is
explicit work-in-progress (Iris Workshop 2025). [ANALYSIS] The closest living
relative to GoLean's "executable semantics first, Iris above" shape — evidence
the ecosystem treats interpreter-level semantics as a first-class Iris substrate.
Nothing concurrency-transferable yet; watch item.

### 4.7 Trillium / Fairis — fair liveness in Iris

**[FACT]** Timany, Gregersen, Stefanesco, Hinrichsen, Gondelman, Nieto, Birkedal,
POPL 2024 (https://dl.acm.org/doi/10.1145/3632851,
https://iris-project.org/pdfs/2024-popl-trillium.pdf, Coq
https://github.com/logsem/trillium). Verified this session: step-indexing
restricts ordinary Iris adequacy to simple safety; Trillium strengthens adequacy
to an **intensional refinement between program execution traces and an abstract
model**, from which trace properties — including liveness — of the model
transfer. Fairis (the concurrent instantiation) proves liveness under **fair
scheduling** with a *fuel* mechanism: threads hold fuel per model role; stepping
a role refuels it; fuel bounds stuttering (unrestricted stuttering is unsound for
liveness), and the simulation maps fair program traces to fair model traces.
The Aneris instantiation refines distributed systems to TLA+ models.

**[ANALYSIS]** The most relevant "fairness infrastructure exists in Iris"
datapoint — and it is *heavy*: a new trace-indexed adequacy, fuel bookkeeping in
every proof, Coq-only. Sane split for the arc: fairness quantifier and statement
live at the trace level over our `Step` relation (first-order, TCB-clean,
Simuliris-style definition); iris-lean is used for safety WP only; liveness-
under-fairness theorems ("this send eventually completes") are out of arc scope,
and Trillium tells us their cost is a new adequacy layer, not an add-on lemma.
Trillium's trace-vs-model refinement is also a statement-shape precedent for
relation-vs-interpreter correspondence, but ours is per-step and needs no trace
adequacy.

### 4.8 Deadlock freedom: the Jacobs line

**[FACT]** Verified this session:
- Jacobs, Balzer, Krebbers, "Connectivity Graphs: A Method for Proving Deadlock
  Freedom Based on Separation Logic", POPL 2022
  (https://dl.acm.org/doi/10.1145/3498662; Coq github.com/julesjacobs/cgraphs).
  Deadlock/leak freedom via progress-and-preservation over an *acyclic topology*
  of threads/channels; separation-logic proof rules correspond to
  acyclicity-preserving graph transformations ("do proofs in separation logic,
  get acyclicity for free").
- Jacobs, Balzer, "Higher-Order Leak and Deadlock Free Locks", POPL 2023
  (https://dl.acm.org/doi/10.1145/3571229): λlock type system; acyclic sharing
  topology; session channels *encoded as locks*; λlock++ for cyclic unbounded
  process networks; mechanized in Coq.
- Jacobs, Hinrichsen, Krebbers, "Deadlock-Free Separation Logic: Linearity Yields
  Progress for Dependent Higher-Order Message Passing" (LinearActris), POPL 2024
  (https://dl.acm.org/doi/10.1145/3632889,
  https://iris-project.org/pdfs/2024-popl-dlfactris.pdf): a **linear** CSL whose
  adequacy gives deadlock and leak freedom "for free from linearity"; model is
  step-indexed over connectivity graphs; Actris amended with linear-session
  restrictions (Wadler-style fused fork+new-channel, making channel ownership
  acyclic); proves GV-style session-type soundness; mechanized in Coq. (Also:
  "Mixtris", mixed-choice multiparty, https://doi.org/10.1145/3798224.)

**[ANALYSIS]** Key structural fact: this line is *not* an extension of mainline
affine Iris — deadlock freedom is a progress property affine logics cannot
deliver (affinity lets you drop the obligation to communicate; linearity or
Iron-style trackable resources are required). The acyclicity/linearity
disciplines also reject legitimate Go programs (Go permits deadlock-prone
topologies; the runtime detects global deadlock and panics). Verdict: deadlock
freedom is a program-specific liveness property outside the arc's claims; our
fail-closed analogue is cheaper and honest — make "all goroutines blocked" a
visible terminal classification in the machine (mirroring Go's runtime deadlock
panic), so deadlocks are observable executions in the differential, not proof
obligations. If GoLean ever wants proved deadlock freedom, LinearActris is the
reference and would be a separate logic layer, not a WP extension.

---

## 5. iris-lean reality check (pinned rev `3877dbec`)

**[FACT]** Manifest pin: `proofs/lake-manifest.json` → `iris` at
`3877dbeccd1b0545c5be7ef73318e8c86acf79ab` (subDir `Iris`); checkout `.git/HEAD`
matches. All facts below at this rev.

### 5.1 What exists TODAY (far more than "base logic")

- **Base logic / algebra**: full CMRA/OFE stack (`Iris/Algebra/*`: Agree, Auth,
  Excl, Frac, DFrac, View, HeapView, GenMap, LocalUpdates, COFESolver, IProp),
  uPred, BI + derived laws, plainly, internal eq, big ops.
- **Proof mode**: a real IPM — `iintro/icases/iapply/imod/iframe/ispecialize/
  iloeb/…` with intro/spec patterns (`Iris/ProofMode/*`), used fluently in
  nontrivial proofs (Spawn.lean, Par.lean read like Rocq IPM proofs).
- **Fancy updates + invariants**: world satisfaction (`Instances/Lib/WSat.lean`),
  `FUpd` (`Instances/Lib/FUpd.lean`, 588 lines), invariants with
  alloc/acc/combine/split (`Instances/Lib/Invariants.lean:33,209,234@3877dbec`),
  **cancellable** (`CInvariants.lean`) and **non-atomic** (`NaInvariants.lean`)
  invariants, namespaces/CoPset.
- **Later credits**: `Instances/Lib/LaterCredits.lean` (692 lines); the WP
  consumes `£ (numLatersPerStep ns + 1)` per step
  (`ProgramLogic/WeakestPre.lean:77`).
- **Ghost libraries**: GhostMap, GenHeap (`BI/Lib/GenHeap.lean`), **ProphMap**
  (`BI/Lib/ProphMap.lean`), Token, MonoNat, ExclAuth/FracAuth/DFracAgree.
- **Language-generic program logic**: `Language` typeclass = per-thread
  `primStep : Expr × State → Obs → Expr × State × List Expr → Prop` + `ToVal`
  (`ProgramLogic/Language.lean:55-100`), thread-pool `Step`/`NSteps`/erased steps
  (114-166), `Atomic` (234-240), `PureExec`, `Context`, plus
  `EctxLanguage`/`EctxiLanguage` and lifting lemmas (`Lifting.lean`,
  `EctxLifting.lean`).
- **The full modern WP**: `wp.pre` with stateInterp over (state, step-count,
  observations, thread-count), later credits, `forkPost`, forked-thread WPs
  (`WeakestPre.lean:69-79`), contractive fixpoint (81-115), `IrisGS_gen` (44-57).
- **Adequacy, the real thing**: `wp_strong_adequacy_gen`
  (`ProgramLogic/Adequacy.lean:174-192`), first-order `adequate` record (result +
  not-stuck over thread-pool executions, 237-244), `adequate_tp_safe` (262),
  `wp_adequacy_gen` (279), `wp_invariance_gen` (318).
- **HeapLang end-to-end**: syntax/semantics as §1 (prophecies + observations
  included), notation, `wp_pures/wp_bind/wp_rec` tactics, primitive laws
  (`wp_rec/wp_fork/wp_alloc/wp_load/wp_store/wp_cmpXchg_fail/wp_cmpXchg_true`,
  PrimitiveLaws.lean:111-292), `Atomic` instances, and verified libraries:
  **Spawn, Par, SpinLock (221 lines, satisfying an abstract `Lock` interface
  class, Lib/Lock.lean:13-44), Quicksort, Landin's knot**.
- **Soundness hygiene**: zero live `sorry` — all grep hits are inside
  comments/commented-out code (`BI/Sbi.lean:598` sits in a block comment ending
  at 599; `Std/PartialMap.lean:791,826,831`, `ProofMode/InstancesUpdates.lean:
  216,221`, `Algebra/CMRA.lean:1081-1082` all commented) [FACT, grep + context].

Gaps vs the Rocq ecosystem [FACT, by grep at this rev]: **no atomic-update /
logically-atomic-triple library** (`atomic_update|AtomicUpdate|atomic_wp`: zero
hits), **no total WP** (`twp`: zero hits), no Actris/iProto, no Trillium-style
trace adequacy, no heap_lang `wp_faa/wp_xchg/wp_free/wp_newProph/wp_resolve`
laws (semantics supports them; laws unwritten — irrelevant to us, we write GoCore
laws).

### 5.2 What GoLean has ALREADY wired (worktree `a38e086`)

**[FACT]** `proofs/GoLeanProofs/Lang.lean:22-47`: GoCore's `Config`/`ExecState`/
`Step` instantiates the bare `Language` (no ectx): `ToVal Config Unit` with
terminal `.next .stop`; `GoPrimStep (c,s) [] (c',s',[])` wrapping the sequential
`Step` with no observations and **no forked threads**; `val_stuck` proved.
`Lang.lean:52-58` wires gen_heap over GoCore's real heap (keyed by base address);
`Lifting.lean` holds the one-step-plus-ghost-update engines (`wp_store_step`);
`Adequacy.lean:27-51` has the concrete functor bundle `GoCoreS` (inv + CoPset +
PosSet + credits + gen_heap views; "mirrors HeapLang's `HeapLangS`") and
`GoCoreGpreS` with ghost allocation as adequacy's job.

### 5.3 Gap analysis for the concurrency arc

**[ANALYSIS, over the facts above]**

| Need | Status | Cost shape |
|---|---|---|
| Concurrent WP over our relation (interleaving, fork) | **Exists generically**: `Language.Step` gives the thread pool the moment `GoPrimStep` emits forked configs and `Config` becomes per-goroutine control against shared `ExecState`. | Cost is GoCore-side machine factoring, not iris-lean work. |
| Fork rule for `go` | Derivable like `wp_fork` (PrimitiveLaws.lean:120-127) — about a page. | Small. |
| Invariants, fancy updates, later credits | Present. | None. |
| Ghost state for channel protocols (auth queues, tokens, counters) | Auth/Excl/Frac/GhostMap/Token/MonoNat present. | Per-protocol constructions, Spawn-sized. |
| Adequacy → first-order readout | `wp_strong_adequacy_gen` + `adequate` present; GoLean bundle pattern proven. | Mechanical (extend `GoCoreS` if new cameras). |
| Channel-step WP laws (physically atomic) | Same shape as existing `wp_store_step`; add `Atomic` instances for channel-step configs. | Moderate — the arc's bread-and-butter. |
| Atomic updates / logically-atomic triples | **Absent.** | Real port; per §3 not needed for primitive channels — defer. |
| Total WP | **Absent.** | Avoid depending on it. |
| Actris/iProto layer | **Absent** (COFE solver exists, so buildable). | Weeks-scale; cheaper substitute = history ghost (§6). |
| Fairness / liveness / trace adequacy | **Absent**; adequacy is safety-only. | Research-scale (Trillium); keep fairness first-order outside Iris. |
| Prophecies | Semantics/observations/ProphMap present; no laws. | Defer; infrastructure ready. |

**[ANALYSIS] Headline:** the gap is dramatically smaller than the prior
"iris-lean = base logic + proof mode." At this rev it is a working concurrent
program logic with strong adequacy and verified concurrent libraries. The arc's
needs are covered *except* atomic updates, Actris, and liveness/fairness — all
three avoidable by design choices we should make anyway. The dominant cost is
GoCore-side (per-goroutine `primStep` factoring + channel-step lifting laws).

**[ANALYSIS] Two design cautions.**
1. *Rendezvous vs per-thread steps*: iris-lean's `primStep` steps one thread with
   others frozen; unbuffered-channel rendezvous is naturally two-thread. It fits
   only if the rendezvous is mediated through shared state (sender parks value/
   blocked-marker in the channel record inside `ExecState`; the receiver's step
   completes the exchange and unblocks the sender) — i.e., blocking is machine-
   visible state, not a joint synchronous step. This also matches Go's runtime
   (`sudog` queues) and is differential-friendly. Record as a machine-design
   decision.
2. *Goroutine identity*: the thread pool is a `List Expr` and thread identity is
   pool position (`Language.lean:114-116`, permutation lemmas 341-369). For
   fairness statements GoLean should carry a stable goroutine ID inside `Config`
   and treat pool position as presentation.

---

## 6. Statement-idiom transfer under the deletion test

Constraint recap (CLAUDE.md; TCB doctrine 2026-08-01): headline statements are
interpreter-level pre/post; Iris is proof machinery only; end theorems must be
understandable with Iris deleted.

**[ANALYSIS] What survives as internal machinery over our Step relation:**

1. **Invariants + ghost state for channel protocols — yes, first-class.** The
   Spawn.lean pattern (token + invariant around a shared cell) transfers verbatim
   to "token + invariant around a channel's queue-in-ExecState". Default proof
   idiom of the arc; needs nothing new.
2. **Actris-style protocol layer — yes as machinery, not in the first arc.** It
   sits above our channel-step laws with a strictly simpler model than Actris's
   own. Adopt only when a target proof (raft's message loops) visibly wants
   session-shaped reasoning; otherwise the history-ghost idiom below suffices.
3. **Logical atomicity — mostly dissolved.** Channel steps are physically atomic
   machine steps; the lifting law *is* the atomic spec. Port AU only for
   Go-implemented sync objects.
4. **Prophecy — keep available, don't use** (§3): select's envelope resolves
   choice at its own step.
5. **ReLoC-style "other semantics as ghost state" — yes**, as the in-logic
   technique for relation-vs-interpreter correspondence under concurrency, if
   proved in-logic at all; a direct Prop-level per-step simulation may remain
   cheaper and TCB-cleaner.

**[ANALYSIS] What the deletion test implies for final channel-spec phrasing:**

- End theorems: **pre/post over joined final states of the thread-pool
  execution**, in exactly the `adequate` shape already in iris-lean
  (Adequacy.lean:237-244): for all executions of `[main]` from a well-formed
  initial state, (a) terminal pools satisfy `φ` over the final `ExecState`, (b)
  not-stuck — which under fail-closed doctrine is itself semantic ("no goroutine
  leaves the envelope"). WP + strong adequacy discharge into a pure `φ : Prop`;
  `adequate` mentions only Config/ExecState/Step. This extends the existing
  GoLean headline pattern to pools; no new statement idiom.
- **Per-channel history predicates stated operationally — yes; the recommended
  substitute for exporting protocol specs.** Internally: an auth-ghost history
  (list of sent values) per channel, synced to the machine's channel queue by an
  invariant. At the boundary: operational statements — "in every reachable
  state, `received(c) ++ buffered(c)` is a prefix of `sent(c)`", or `φ` over
  final states ("consumer's output is a permutation of producers' sends") — all
  definable by folding the interpreter's state/trace, zero iProp. The ghost
  history is the proof's shadow of an operational quantity; that is what makes
  it deletable.
- **Fairness quantifier: first-order over Step traces** (Simuliris-style fair
  scheduling, §4.3), zero Iris; sequential conservation as safety-flavored
  simulation unless termination-preservation is explicitly demanded (then:
  Simuliris-shaped meta-proof, not step-indexed WP).
- **Deadlock: an envelope classification, not a theorem** (§4.8): "all goroutines
  blocked" becomes a visible terminal outcome mirroring Go's runtime deadlock
  panic, keeping the differential oracle honest.

---

## Appendix: sources verified this session

- Simuliris POPL 2022: https://dl.acm.org/doi/10.1145/3498689 /
  https://iris-project.org/pdfs/2022-popl-simuliris.pdf
- Actris POPL 2020: https://dl.acm.org/doi/10.1145/3371074 /
  https://iris-project.org/pdfs/2020-popl-actris-final.pdf /
  https://iris-project.org/actris/ / https://gitlab.mpi-sws.org/iris/actris
- Actris 2.0 (LMCS 2022): https://arxiv.org/pdf/2010.15030
- Trillium/Fairis POPL 2024: https://dl.acm.org/doi/10.1145/3632851 /
  https://iris-project.org/pdfs/2024-popl-trillium.pdf /
  https://github.com/logsem/trillium
- Cosmo ICFP 2020: https://dl.acm.org/doi/10.1145/3408978 /
  https://iris-project.org/pdfs/2020-icfp-cosmo-final.pdf
- Connectivity graphs POPL 2022: https://dl.acm.org/doi/10.1145/3498662
- Higher-order leak/deadlock-free locks POPL 2023:
  https://dl.acm.org/doi/10.1145/3571229
- LinearActris POPL 2024: https://dl.acm.org/doi/10.1145/3632889 /
  https://iris-project.org/pdfs/2024-popl-dlfactris.pdf
- Osiris ICFP 2025: https://iris-project.org/pdfs/2025-icfp-osiris.pdf
- Iris-WasmFX: https://dl.acm.org/doi/10.1145/3808271

From-memory citations (not re-fetched): RustBelt POPL 2018; ReLoC LICS 2018 /
LMCS 2021; TaDA ECOOP 2014; "The Future is Ours" POPL 2020; iGPS ECOOP 2017;
iRC11 POPL 2020; Iris-Wasm PLDI 2023; Iris JFP 2018 (logically atomic triples);
Multris OOPSLA 2024; Actris channel-implementation detail (two lock-protected
linked-list buffers + spin-retry recv).
