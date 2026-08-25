# The Iris reuse map — campaign machinery vs iris-lean, the ported
# projects, and the classics (2026-08-24)

Read-only survey, [AGENT] throughout, dispatched by the campaign log's
**[USER] addendum (2026-08-24), the Iris sharpening of clever-tricks**
(`docs/raft-campaign-log.md:710`): *use the machinery where it exists;
build Iris-COMPATIBLE machinery where it is missing; reuse ideas
freely; NOTICE where our custom solutions converge on Iris ideas and
map them into reusable proof infra.* It EXTENDS, and does not restate,
the pre-campaign delta scan
(`docs/2026-08-20_iris-lean-delta-scan.md`, rows R1–R13 + the [USER]
rulings of §6) to the machinery the campaign itself built: the Sym /
TableExt window transport, the FastEval γ-simulation, the Arc-4 seam's
layer C, the handler-equation form, and the kit's frame/footprint
layer.

Nothing here changes a pin, a gate, a statement, or a proof. Its
outputs are verdicts and a prioritized shortlist.

---

## 0. The finding that frames every section

**The campaign has been proving in a wing of the tree that contains no
Iris at all.** Measured this session over `proofs/GoLeanProofs`:

| module tree | files importing `Iris` |
|---|---:|
| `Sym/` | **0** |
| `FastEval/` | **0** |
| `Frame/` | **0** |
| `Specs/Raft/` | **0** |

(`grep -rl "import Iris"` per directory; the whole `proofs/` tree has
19 Iris-importing files out of 259 — `Lang`, `LangC`, `LangD`,
`Ghost`, `Adequacy`, `HeapBridge`, `Lifting`, `SurfaceExit`,
`Tactics/GoWalk`, `Specs/GoldenSliceWP`, and the nine `Laws/*`.)

This is not an accident and not a defect: it is the recorded split the
kit guide states outright —

> `go_walk` is a different layer. `Tactics/GoWalk.lean` automates the
> Iris WP walk … not the direct segment method this guide indexes.
> (`docs/kit-guide.md:813`)

— and it is forced at the top by the statement-TCB doctrine: T1's
statement is `∀ fuel ch r, twinRun fuel ch = .ok r → r.values[0]? =
some (.int 0 .int)` over `runProgramM`, with the module header
stating **"No Iris, no relation, no accelerator (§3.1)"**
(`proofs/GoLeanProofs/Specs/RaftAgreement.lean:15`, statement at
`:49`).

So every verdict below answers a *proof-side* question, never a
statement-side one, and the honest baseline is: **Iris is optional for
this campaign in a way it is not for Perennial**, because the twin's
seam is sequential. Iris's leverage is concurrency-mediated resource
sharing; where the proof obligation has no sharing, an Iris carry buys
vocabulary and composition, not power. That single economic fact
drives the NOW/post-T1 split in §7.

**The bridge exists, though, and it is proved.** If we ever want the
Iris carry, the pipe from an Iris WP proof down to executable
reachability is already built in this repo and is not speculative:

- `proofs/GoLeanProofs/SurfaceExit.lean:145` — `goInvariant_of_wp`:
  from `inv N ⟦I⟧ ∗ ⟦P'⟧ ⊢ WP (Config.exec prog env₀ .stop) {{ _, True }}`
  conclude the native `GoInvariant … I` judgment;
- `proofs/GoLeanProofs/Adequacy.lean:280` — `go_heap_invariance`;
  `:141` — `go_heap_adequacy`; `:36` — the concrete `GoCoreS` functor
  bundle;
- `proofs/GoLeanProofs/Surface.lean:266` — `steps_of_reachableExec`,
  the executable→relation containment (`stepFn_sound` chained,
  `GoLean/GoCore/MachineSound.lean:44`).

The assertion language on the native side is a deep-embedded SL
(`Surface.lean:64`: `emp | pure | pointsTo | sep | ex`), which is
expressive enough to state "∃ N, the heap describes N ∗ ⌜verdiInv N⌝".
So a layer-C-on-Iris is a *cost* question, not a *feasibility*
question.

---

## 1. Sym / TableExt window transport

### What it does

`Sym/Domain.lean` defines a scalar abstract domain (`ScalarDom`, with
concrete instance `cdom` and symbolic instance `symDom`) plus deep
first-order term languages `SymInt`/`SymBool` and their valuation γ.
`Sym/Conc.lean` gives one concretization family over an `Interp D`
pack, with a soundness pack (`Interp.Sound`) whose fields are the
per-op scalar leaves. `Sym/Walk.lean` + `Sym/Refine.lean` run the
mirror step function to a fixed budget and transport the result:

> `proofs/GoLeanProofs/Sym/Refine.lean:37` — `symEvalWindow_refines`:
> `symEvalWindow budget S C = (n, S', C') → ∀ ρ σ ch, stepFnIter n (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C', γS ρ σ S', ch)`

`Sym/TableExt.lean` (2,052 lines, campaign Arc 4) layers a type-table
input `T` fully additively over that core — one overridden step arm
(`.next (.storeK …)`), everything else delegating — with exactly one
new premise, `SubTable T U := ∀ id d, TypeEnv.lookup T id = some d →
TypeEnv.lookup U id = some d` (`TableExt.lean:51`), and
`SubTable.nil` making the shipped theorems the degenerate instance.
The evaluator **quits** rather than erring; a quit at step `n+1`
yields the `n`-step fact, so the theorem has no error channel and no
side conditions.

### Nearest analogs, with evidence

**iris-lean at the pin (`3877dbec`) — none.** Verified this session:
`grep -rn "native_decide" Iris/` = **0**; a search for
`symbolic`/`SymState`/`abstract interpretation` over `Iris/` returns
no files. Its stepping is goal-directed tactic automation:
`Iris/Iris/HeapLang/ProofMode.lean:299` (`tac_wp_bind`), `:332`
(`tac_wp_pure`), `:346` (`wp_pure` elab), `:373-374` (`wp_pure`,
`wp_pures`), over primitive laws at `HeapLang/PrimitiveLaws.lean:182`
(`wp_load`) / `:214` (`wp_store`).

**Perennial — goal-directed only, and it tried our route twice and
abandoned both.** (Checkout caveat: `deps/perennial` is a **shallow
clone**, `git rev-list --count HEAD` = 1, tip `43d4efab`, dated
2026-07-01; the old `goose_lang_v1` refinement stack is absent from
this snapshot, so anything below is "in this checkout", not "in
Perennial".)

- The live automation: `new/golang/theory/proofmode.v:17` (`Class
  PureWp`, an extensible typeclass step table), `:172` (Ltac2
  `walk_expr`, the evaluation-context search), `:254-256`
  (`wp_pure`/`wp_pures`); `new/golang/theory/auto.v:87`
  (`wp_auto_lc` — `progress (repeat (first [...]))`, Perennial's
  symbolic executor), `:66` (`wp_start`), `:277` (`wp_apply`).
  The step oracle is `typeclasses eauto`, and the "symbolic state" is
  the IPM context, not a datatype.
- **Dead attempt #1, and it is our exact shape.**
  `src/Helpers/Transitions.v` carries a deeply-embedded
  nondeterministic transition syntax (`:29`), its denotation
  `relation.denote` (`:228`), an **executable evaluator that resolves
  nondeterminism from a hint list** `interpret (hints : list Z)`
  (`:123`), and the one-directional soundness theorem

  > `src/Helpers/Transitions.v:282` — `Theorem interpret_sound {T} (tr: transition Σ T): forall hints s s' hints' v, interpret hints tr s = Some (hints', s', v) -> denote tr s s' v.`

  That is `symEvalWindow_refines`'s and `stepFast_ok`'s shape, with
  the hint list playing our `Choices` stream. **It has no consumers.**
  Verified: `grep -rn "interpret" --include=*.v src new` outside
  `Transitions.v` returns only prose (`src/goose_lang/locations.v:19`,
  `src/program_logic/crash_weakestpre.v:20`) and one stale TODO,
  `src/goose_lang/ffi/disk_ffi/impl.v:88` ("use Sydney's executable
  version from disk_interpreter.v"), pointing at a file that is not in
  this checkout. What *is* used from that module is the tactic pair
  `monad_simpl`/`monad_inv` (`:471`, `:488`), consumed at
  `new/golang/theory/proofmode.v:82-87`.
- **Dead attempt #2, and it is a reflective symbolic executor.**
  `new/experiments/checker__nobuild.v`: reified syntax (`:10`),
  concretization `interp` back to GooseLang (`:33`), a Ltac2 reifier
  (`:61`), a **symbolic state datatype** `go_prop.t` (`:110`),
  symbolic steps `step_pure`/`step_ref_ty` (`:200`, `:207`), a Gallina
  `walk_expr` (`:214`), and a fuel-driven `pure_steps` (`:239`) probed
  with `vm_compute` (`:262`). It is excluded from the build
  (`Makefile:4`, `:7-8` filter `*__nobuild.v`), is internally broken,
  and — decisively — **has no soundness theorem** back to
  `base_step`. Our `Refine.lean:37` is precisely the missing piece.

**The classics.** Symbolic execution (King, CACM 1976), abstract
interpretation's γ/soundness discipline (Cousot & Cousot, POPL 1977),
and computational reflection with a verified evaluator (the CompCert
lineage). **No local artifact** for any of these papers — cited from
memory, flagged as such. RefinedC/Lithium's goal-directed automation
and Diaframe are the obvious modern comparanda and there is **no local
checkout of either** (`ls deps/` = `go goose iris-lean perennial
raft`); I make no claims about them beyond naming them as unchecked.

### Verdict

**NO-ANALOG (reuse direction) + IDEA-ALREADY-CONVERGED (export
direction).** There is nothing in iris-lean or this Perennial
checkout to import; the two things closest to Sym in the Iris
ecosystem's Rocq side are both dead code, and one of them lacks
exactly the theorem we have. Do **not** rebase Sym onto Iris — that
would trade a proved, program-generic, ∀ρ∀σ∀ch transport for a tactic
loop, and the kit guide's measured routing table
(`docs/kit-guide.md:212-252`) already prices the alternatives.

Two genuine reuse items fall out anyway:

1. **`SubTable T σ.types` is the un-Irised twin of our own
   `GoCoreGS.types` pin.** `proofs/GoLeanProofs/Ghost.lean` pins
   `types`/`prog`/`methods` in the ghost state precisely because
   `∀σ`-quantified premises mentioning named types are otherwise
   vacuous (the `types` field's docstring, `Ghost.lean:41-58`, argues
   it at length,
   with `Specs/GoldenQuorumPin.typeEnv_pin_is_load_bearing` as the
   kernel-checked demonstration). `TableExt`'s `SubTable` is the same
   fact re-derived one wing over, in weakened (sub-table, not
   equality) form. **Convergence — map it:** the state-interpretation
   pin and the `SubTable` premise should cite each other, and the
   weakened form is the better one (it is what makes a window emitted
   at the pin's table transport into any extending state).
2. **The choice-stream-as-hint-list convergence** with
   `Transitions.v:123` is worth one sentence in the Sym design note's
   LINEAGE line: our determinizer is the classic one.

---

## 2. The FastEval γ-simulation

### What it does

`proofs/GoLeanProofs/FastEval/` (≈3,600 lines) mirrors the exercised
fragment of the interpreter over a **binary-trie heap** (`Heap.lean`:
`HeapT`, `HeapT.get/set`, `WF t na := ∀ a, (t.get a).isSome ↔ a < na`,
and the range-dump abstraction `γH t na : Heap`), with
`γF σF : ExecState` lifting it to whole states, and a **one-directional**
simulation: `stepFast σF c ch = .ok (…) → stepFn (γF σF) c ch =
.ok (…)`. Unexercised arms are fail-closed stubs whose simulation
cases are vacuous; pure helpers are called at the genuine abstraction
image `γF σF` so the sim proofs line up syntactically
(`docs/2026-08-22_fasteval-design.md` §2(a)/(b)). It is an accelerator,
never in a statement closure.

### Nearest analogs, with evidence

**Is it resource-algebra-shaped? No.** It is a plain functional data
refinement — an α/γ pair between two *executable* state
representations. Iris's resource algebras abstract *ownership*, not
representation; the RA-shaped counterpart of `γF` in our own tree is
the state interpretation, `genHeapInterp (heapToMap σ.heap)`
(`proofs/GoLeanProofs/Adequacy.lean:141`, with the state
interpretation built at `:171-174`), i.e. the map from a
concrete heap into the ghost carrier. So the *idea* already appears
twice in this repo, in two wings, for two purposes.

**Perennial: a firm negative on data refinement of state
representations.** Searched for `refines`, `bisim`, `forward_sim`,
`absR`, `abs_rel`, `sim_rel`, `abstraction` across `src` + `new`:
zero definitional hits; the only conceptual mention is a stale comment
at `src/goose_lang/lang.v:1469`. What Perennial does instead is
**representation predicates** (`new/golang/theory/map.v:59`
`own_map_def` relating a GooseLang map value to a `gmap`;
`slice.v:17` `own_slice_def`) and **axiomatized
representation-independence**: the whole Go data layer is a typeclass
of laws — `new/golang/defn/postlang.v:101-127`
(`Class GoSemanticsFunctions`, including `is_map_pure`),
`new/golang/defn/map.v:58-120` (`Class MapSemantics`),
`new/golang/defn.v:6-13` (`Class go.Semantics`) — **with no instance
anywhere in the checkout**. Perennial buys representation-independence
by never committing to a representation; we buy it by proving one
representation simulates another. These are opposite strategies and
ours is the one compatible with a differentially-validated executable
interpreter.

The single local artifact with FastEval's exact one-directional shape
is again `src/Helpers/Transitions.v:282` (§1) — dead code.

**iris-lean:** `Iris/Iris/Std/HeapInstances.lean` supplies
`ExtTreeMap`-backed `PartialMap`/`LawfulPartialMap`/`FiniteMap`/
`UnboundedHeap` instances (this is what `GoHeapF` uses, per the delta
scan §2a). That is an *interface* over a tree map on the **ghost**
side; it is not a proved simulation, and it cannot serve FastEval's
role, which requires cheap **kernel** reduction over structural
recursion (`docs/2026-08-22_fasteval-design.md` §1.3: 9.4 ms/op,
0.44 MB/op at 36k entries, `WellFounded.fix` explicitly ruled out).

**The classics.** Data refinement / simulation (Hoare, *Proof of
correctness of data representations*, Acta Inf. 1972;
He–Hoare–Sanders' downward/upward simulation), and verified-compiler
memory-model refinement. **No local artifact** — from-memory citations.

### Verdict

**NO-ANALOG for the accelerator role (keep ours, do not rebase) +
IDEA-REUSED-ALREADY for the abstraction-function pattern.** The map
to record: `γF`/`γH` : accelerator :: `heapToMap`/`genHeapInterp` :
ghost carrier — one α, two consumers. If FastEval ever needs a second
representation (it will not, on the current route), the lesson from
Perennial's `go.Semantics` is that the *interface-with-laws* route
exists and is cheaper up front and unusable for us at the bottom,
because our bottom must execute.

One honest gap: FastEval's simulation is success-direction only, by
design (§2(a)). That is the same directional restriction as the
executable frame theorem (§5) and as `stepFn_sound`. It is fine for
∃-witnesses and for transporting ∀-facts *down*, and it is exactly
what a reviewer should re-check if anyone ever states a ∀-claim over
`stepFast`.

---

## 3. The Arc-4 seam's layer C

### What it does

`docs/2026-08-22_campaign-arc4-seam-design.md` §2: **(A)** a total,
first-order abstraction function `absState`/`absRaftNode`
(`proofs/GoLeanProofs/Specs/Raft/AbsState.lean`, `Option`-valued,
fail-closed, plus a WF-pack of executable side facts); **(B)**
per-handler interpreter-run equations; **(C)** the round induction —
the driver's loop lifts each round to one abstract net step, Arc 3's
`refined_raft_net_invariant` instances hold along the abstract trace,
and per-check "checker-implication" lemmas show the in-program S1–S3
checks compute predicates the spec invariants imply, so `violations`
never increments.

### Nearest analogs, with evidence

**iris-lean at the pin: nothing.** A search for
refinement/simulation identifiers over `Iris/` returns a single
incidental file. iris-lean is the logic, not a refinement framework.
It does supply every *ingredient*: `Algebra/Auth.lean:30`
(`AuthViewRel`, the auth/frag construction), `Algebra/Excl.lean`,
`Instances/Lib/GhostMap.lean:32`/`:40` (`ghost_map_auth` /
`ghost_map_elem`), `Instances/Lib/Invariants.lean:33` (`inv`), `:209`
(`inv_alloc`), `:234` (`inv_acc`), and adequacy at
`ProgramLogic/Adequacy.lean:247` (`adequate_alt`) / `:279`
(`wp_adequacy_gen`).

**Perennial (this checkout): the classic ReLoC-style refinement stack
is ABSENT, but two partial spines exist and one is `Qed`-complete.**

- *Absent*: `spec_assert.v`, `refinement.v`, `refinement_adequacy.v`,
  `spec_ffi`, and every identifier of that stack (`source_ctx`,
  `spec_ctx`, `source_step`, `j ⤇`, `tpool_map`, `cfg_auth`) —
  zero hits tree-wide. `src/program_proof/` does not exist here.
  This is the shallow-clone caveat again; do not read it as
  "Perennial doesn't do refinement".
- *Present and complete — the Actris/DSP spine.* The abstract program
  is a guarded-recursive session protocol `iProto Σ V`
  (`new/golang/theory/chan/idioms/dsp/dsp_ghost_theory.v:67`), the
  spec state is carried as **excl-auth ghost state over the abstract
  program itself**:

  > `dsp_ghost_theory.v:303` — `iProto_own_frag γ p := own γ (◯E (Next p))`
  > `dsp_ghost_theory.v:306` — `iProto_own_auth γ p := own γ (●E (Next p))`
  > `dsp_ghost_theory.v:315` — `iProto_ctx γl γr vsl vsr := ∃ pl pr, iProto_own_auth γl pl ∗ iProto_own_auth γr pr ∗ iProto_interp vsl vsr pl pr`

  the concrete↔abstract coupling lives in an **ordinary Iris
  invariant** — `dsp.v:70` `dsp_session_inv` (holding the *concrete*
  Go channel state `own_chan …` next to `iProto_ctx`, tied by a
  `buffer_matches` conjunct (`dsp.v:58`)), wrapped at `dsp.v:106`
  as `dsp_session … := is_chan … ∗ is_chan … ∗ inv N (dsp_session_inv …)`
  — and the abstract program is **stepped by ghost update in exchange
  for the physical step**: `dsp_ghost_theory.v:1155` (`iProto_send`),
  `:1175` (`iProto_recv`), over the primitive `:939`
  (`iProto_own_auth_update`).
- *Present and complete — the closest thing to our round induction.*
  `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_dsp.v:79`
  (`wp_Serve`): a Go server loop is shown to follow an **infinite
  guarded-recursive abstract protocol** `service_prot` (`:72`), with
  the loop-body proof driven by `wp_for "IH"` at `:113`, `Qed` at
  `:140`. This is layer C's shape — an implementation loop matching an
  abstract trace, one round at a time, carried by ghost ownership.
- *Present but sketched — the etcd model spine, and it names our
  vocabulary exactly.* The spec is an interaction-tree-style effect
  program (`new/proof/go_etcd_io/etcd/client/v3_proof/model.v:8`,
  `:21`, `:78`) over an abstract state record (`:55-75`), and the
  abstract state is carried as `ghost_var γ q σ` in a
  predicate-transformer handler (`.../v3_proof/spec.v:19`). The
  leasing proof literally defines abstract steps and their ghost
  updates —
  `new/proof/go_etcd_io/etcd/client/v3/leasing_proof/protocol.v:142`
  (`step_Lock`), `:150` (`take_step_Lock`), `:159` (`step_Commit_Put
  := interp (handle_etcdE 0) (Put put_req) s s' (inr resp)`), `:166`
  (`take_step_Commit_Put`) — **but the entire section is inside a Rocq
  comment (`(*` at line 84, `*)` at line 203)**, and the neighbouring
  `spec.v` lemma is `Abort`ed with an `admit` (`spec.v:61`). Treat as
  a design sketch, not as prior art that works.
- *Adequacy shape*: Perennial's is safety+postcondition+invariant over
  crash-epoch traces (`src/program_logic/recovery_adequacy.v:484`
  `recv_adequate`, `:517` `wp_recv_adequacy_inv`), **not** trace
  inclusion. There is no "concrete traces ⊆ abstract traces" theorem
  in this checkout.

**The classics.** ReLoC (Frumin–Krebbers–Birkedal, LICS 2018 / LMCS
2021) is the canonical "hold the other semantics as ghost state"
refinement judgment; Simuliris (POPL 2022) is the
termination-preserving variant. Both are recorded locally as
**from-memory citations** in `docs/2026-08-06_concurrency-research-iris-ecosystem.md:233`
and `:247` — that doc is the local artifact, the papers are not.
Verdi's ghost-refinement decomposition (Arc 3's actual ancestor) has
no checkout in this worktree either (`deps/verdi*` absent here).

### Verdict

**REBASE-COMPATIBLE, cost class L, and post-T1 — with one XS piece to
do NOW.**

The rebase is real and its shape is precisely determined by the local
prior art:

- carry `absState`'s image as **auth/frag ghost state** (`Auth`,
  `Algebra/Auth.lean:30`, or `ghost_map`), exactly as
  `iProto_own_auth/frag` carries the abstract protocol
  (`dsp_ghost_theory.v:303-306`); Arc 3's invariants become a pure
  side-condition on the authoritative half;
- the coupling becomes an `inv N` in the `dsp_session_inv` mould
  (`dsp.v:70`), and layer B's equations become ghost-update lemmas of
  the `iProto_send` shape (`:1155`);
- the round induction becomes `wp_for "IH"`-style loop induction over
  the driver, `channel_dsp.v:113`'s shape;
- the exit is already ours: `goInvariant_of_wp`
  (`SurfaceExit.lean:145`) → `go_heap_invariance` → the executable
  reachability T1 speaks.

**Two honest obstructions, both load-bearing for the cost class.**
(1) An Iris invariant can only be opened around one *atomic* step, and
a round spans thousands of machine steps — so the abstract state must
be *owned and threaded* through the WP (ReLoC's `source j e`;
Perennial's `iProto_own` and `ghost_var γ 1 σ`), with `inv` reserved
for what is genuinely shared. Since the twin is a single-goroutine
driver, **there is nothing shared, so the invariant buys nothing and
the ghost thread buys only bookkeeping we already get from
`absRaftNode σ = some N`.** (2) The rebase requires layer B's
equations to be WP proofs; the A4-U1 pilot verdict already **refuted**
the hand-walk cost at that granularity
(`docs/2026-08-22_campaign-arc4-seam-design.md:108-127`: 3,233 steps,
~9 proof lines per step at leaf granularity), which is why layer B was
re-based on Sym in the first place. Rebasing layer C alone, over
Sym-proved layer B equations, is possible but then the WP is doing no
work: the equations arrive as `stepFnIter` facts and must be lifted
one-by-one into the logic.

**Therefore: post-T1**, and revisit the moment T1's scope acquires
real concurrency (multiple goroutines with shared state), where the
verdict flips hard.

**The XS piece NOW** (already implied by the A4-U5 directive): restate
layer C in explicit **forward-simulation** vocabulary — name the
coupling relation `R σ N` (today it is implicit in
`absRaftNode σ = some N`), state the round step as
`R σ N → step σ σ' → ∃ N', specStep N N' ∧ R σ' N'`, and give the
design note its LINEAGE line (ReLoC/Actris for the ghost-carried
variant; Verdi's ghost refinement for the shape we actually use). That
is what turns a later Iris carry into a *restatement* rather than a
re-derivation, and it costs a doc edit.

---

## 4. The handler-equation form

### What it does

`proofs/GoLeanProofs/Specs/Raft/BfEquation.lean:121` —
`becomeFollower_handler_eq`:

```
∃ σfin,
  stepFnIter 3234 (γS ρ σ uS0) (γC ρ uC0) (c₁ :: c₂ :: c₃ :: c₄ :: ch)
    = .ok (.next .stop, σfin, ch)
  ∧ absRaftNode (γS ρ σ uS0) ⟨0⟩ = some ⟨0, ρ.ints 1, …⟩
  ∧ absRaftNode σfin ⟨0⟩ = some (specBecomeFollower ⟨0, …⟩ 0 (ρ.ints 9))
```

with a §3.3 discharge witness at concrete values (`:160`). Composition
is `stepFnIter_chain` — visibly, a twelve-deep nest at
`BfEquation.lean:84-108`.

### Nearest analog, with evidence

**The idiom is Perennial's, near-verbatim, in Texan-triple form:**

> `new/golang/theory/chan/idioms/dsp/dsp.v:226` —
> ```coq
> Lemma wp_dsp_send (lr_chan rl_chan : loc) γ (v : V) (p : iProto Σ V) :
>   {{{ (lr_chan,rl_chan) ↣{γ} <!> MSG v; p }}}
>     chan.send t #lr_chan #v
>   {{{ RET #(); (lr_chan,rl_chan) ↣{γ} p }}}.
> ```

Pre: the abstract program sits at "about to send `v`". Post: running
the *implementation* has advanced it to `p`. Our pre/post pair
`absRaftNode σ = some N` / `absRaftNode σfin = some (specH N args)` is
**the same statement with the ghost resource replaced by a projection
function**. Companions: `wp_dsp_recv` (`:395`), `wp_dsp_close`
(`:411`); the HOCAP/atomic-update spelling is
`new/proof/go_etcd_io/raft/v3_proof/protocol.v:103`
(`wp_node__Propose`, whose precondition consumes an update advancing
the abstract raft log — `Admitted` at `:141`), and the generic
logically-atomic notation is `src/program_logic/atomic.v:7-61`
(TaDA-style `<<< ∀∀ … >>> e <<< ∃∃ … >>>`). The `step_X` / `take_step_X`
naming that matches our vocabulary most literally is
`leasing_proof/protocol.v:142-195` — commented out (§3).

### Where ours differs, honestly

1. **Exact step count** (`stepFnIter 3234`) rather than a WP. That is
   *stronger* — it carries termination and a fuel measure — and a
   partial-correctness WP would lose it. iris-lean master (not the
   pin) has `ProgramLogic/TotalWeakestPre.lean` + `TotalAdequacy` +
   `TotalLifting` (delta scan §1b), which is the carrier that would
   preserve it.
2. **Choice-prefix quantification** (`c₁ c₂ c₃ c₄`), with the
   conclusion choice-INDEPENDENT because the picked keys land only in
   latitude-bearing spots (`BfEquation.lean:20-25`). Perennial's
   prophecy/observation channel is the nearest device and it is
   threaded through adequacy as `κs` without ever being constrained —
   no local analog for a *choice-indexed* handler equation.
3. **Address-concrete** (`docs/2026-08-22_campaign-arc4-sym-extension-design.md:190`)
   — see §5(d).
4. **Composition by explicit chaining** rather than by frame. This is
   the one place where the Iris form is straightforwardly better: a
   twelve-deep `stepFnIter_chain` nest is what the bind rule and
   `iFrame` exist to eliminate.

### Verdict

**IDEA-REUSED-ALREADY (converged, exact mapping) + REBASE-COMPATIBLE
at the statement level, cost M — post-T1.**

Record the mapping now (`absRaftNode`-equality pair ↔
`iProto_own`-frag pre/post pair ↔ `take_step_X` ghost update), keep
the equations' pre/post explicitly factored so a later swap of
"projection equality" for "owned ghost" is mechanical, and add the
delta-scan reuse row below (§6) so the pin move's payoff is scored
against the campaign, not only against channel-logic.

---

## 5. The kit's frame / footprint machinery

This is really **four** things with one name, and separating them is
most of the value of this section.

### (a) `proofs/GoLeanProofs/Frame/` — the executable frame theorem

Not an Iris frame rule at all: it is **command locality up to
fresh-address renaming**, proved on the executable machine.
`Frame/Sim.lean` (`FrameSim ρ na₀ na fr σ σF`, `ExSim`),
`Frame/Transfer.lean:29` (`stepFnIter_sim`), `execStmtLoop_ren`,
`Frame/AllocIndep.lean` (`allocatorIndependence` — the
address-quotient corollary), `Frame/Threshold.lean` (the shift/rebase
lift), plus per-layer commutation modules (`Plans`, `HeapOps`,
`StrictOps`, `Values`, …; ~11k lines total). Design of record:
`docs/2026-08-13_executable-frame-theorem.md`, whose §1 opens by
recording the [USER] framing — *"this is the COMMAND-LOCALITY property
from separation logic"* — and whose §5c cites the classics by name:
Yang & O'Hearn 2002 (safety monotonicity + frame property),
Calcagno–O'Hearn–Yang LICS 2007 (local actions), and the
Banerjee–Naumann location-bijection lineage
(`docs/2026-08-13_executable-frame-theorem.md:252`). **No local
artifact for those papers** — from-memory citations inside our own
doc.

**Analog search result: none, in either checkout, and this is a firm
negative.** Perennial has **zero** occurrences of "footprint"
(`grep -rni footprint --include=*.v src new` = 0) and **no frame rule
for the step relation** — framing there is exclusively a property of
the separation-logic connectives, obtained free from the resource
algebra (`src/program_logic/weakestpre.v:327`, the `Frame` instance
for `WP`). iris-lean likewise proves nothing about a step relation.

**Verdict: NO-ANALOG, and correctly so — keep ours.** The executable
frame theorem is *upstream* of Iris: it is the semantic fact that
justifies a frame rule, which Iris assumes by construction when it
picks an RA. Duplication is impossible in that direction. Its LINEAGE
line is already written (Yang/O'Hearn locality + location bijections);
it should be quoted in the design note's header, not only in §5c.

**One cheap, real hygiene item: the name collides.** `GoLean.Frame` vs
Iris's `Frame` typeclass (`Iris/Iris/ProofMode/Classes.lean:189`,
with 355 lines of instances in `ProofMode/InstancesFrame.lean`) name
completely different things, and the campaign now has readers in both
wings. Either rename the namespace (`GoLean.Locality` /
`GoLean.Relocation`) or put a two-line disambiguation at the head of
`Frame/Sim.lean`. Prefer the note; a rename is churn.

### (b) `StepKit.DeadFrom` / `FreshFrom` — the actual footprint predicate

`proofs/GoLeanProofs/StepKit.lean:463` —
`DeadFrom (dead : Heap) (na : Nat) := ∀ x, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none`,
with `.push/.push2/.push3/.set/.mono/.lt_of_lookup` (`:468-534`) and
the `FreshFrom` view at `:535`; kit routing at
`docs/kit-guide.md:179-211`.

**This one genuinely duplicates what Iris gives free.** Under
`gen_heap`, you never state absence: allocation *hands you* a fresh
`ℓ ↦ v` and the authoritative map does the bookkeeping; the
"everything ≥ na is absent" invariant is exactly the content of the
auth half. Our own tree already contains the instance
(`Adequacy.lean:171-174`'s `genHeapInterp (heapToMap σ'.heap)` with
the `HeapWf` conjunct).

**Verdict: REBASE-COMPATIBLE, cost S–M — but conditional.** It is only
worth doing if the surrounding proof moves to the WP wing (§3);
standalone, the `DeadFrom` algebra is six lemmas and pays for itself.
Log the convergence, do not act on it now.

### (c) iris-lean's `Frame`/`iframe` — nothing of ours duplicates it

Our tree uses `iframe` 26 times (delta scan §2b-6) and declares zero
`Frame` instances. The delta scan's rows R1 (`AddModal`/`ElimAcc`,
retiring the 393-site modality dance), R2 (`iinv`), R3 (`AbstractWP`)
remain the live duplication findings on the Iris wing and are
**unchanged by this survey** — they bite `Laws/*` and the parked
channel logic, not the campaign's Sym/FastEval/Frame/Raft modules,
which touch no Iris at all.

### (d) NEW — the reuse item the A4-U5 directive should actually take

The A4-U5 dispatch targets the **address-concrete handler fixtures**
(`docs/raft-campaign-log.md:689`, and the caveat as recorded at
`docs/2026-08-22_campaign-arc4-sym-extension-design.md:190`: mirror
heaps are concrete-keyed, so transported windows are value-symbolic
but address-concrete). The Iris ecosystem's answer to exactly this
problem is a **field-granular focusing lens with generated
instances**, and it is small:

> `new/golang/theory/mem.v:78-84` —
> ```coq
> Class AccessStrict {PROP : bi} (A A' P P' : PROP) :=
>   { access_strict : P -∗ A ∗ (A' -∗ P') }.
> #[global] Hint Mode AccessStrict + ! ! - - : typeclass_instances.
> Class Access {PROP : bi} (A A' P P' : PROP) := { access : P -∗ A ∗ (A' -∗ P') }.
> ```

`tac_wp_load`/`tac_wp_store` (`mem.v:105`, `:126`) take an `Access`
instance as an argument and the tactic discharges it by typeclass
search, failing with *"could not find a points-to in context covering
the address"* (`mem.v:164`, `:179`) — i.e. **the instance search IS
the footprint search**. The instances are machine-generated per struct
field by goose (`deps/goose/proofgen/tmpl/types.tmpl:65-77`, emitting
`<T>_access_load_<f>` / `_access_store_<f>`), solved by
`new/golang/theory/auto.v:462`; a worked instance is
`new/generatedproof/sync.v:107-159`
(`Cond_access_store_L : AccessStrict (l.[Cond.t,"L"] ↦ …) … (l ↦ v) (l ↦ (v <|Cond.L' := L'|>))`).
Volume: 76 such instances for `raft/v3/raftpb` alone. The bi-level
generalization is `src/Helpers/PropRestore.v` (`Restore_def R P Q :=
P ∗ □(P -∗ Q -∗ R)`, `:12`, with `IntoSep` instances at `:47`, `:70`,
`:82`).

Note the contrast with our current answer: **TableExt makes
whole-struct re-normalization *computable* inside a window; the lens
makes a store *touch one field* and frame the rest.** Both are
legitimate; only the lens generalizes to a symbolic base address, and
it is the one that scales to a struct with 33 fields — which is
exactly `raft.raft` (`Specs/Raft/AbsState.lean`, "a `.struct
⟨"raft.raft"⟩` value of ~33 named fields").

**Verdict: IDEA-REUSE, adopt NOW as A4-U5's shape.** Not an import
(it is Rocq, and it lives on Perennial's WP); a *pattern*: a
`StructAccess`-style focusing class over our heap-cell algebra, with
per-field instances generated from the pinned lowering's struct table,
consumed by the kit's store lemmas. Cost class S–M, no Iris
dependency, and it is the classic-ward move the clever-tricks
watch-list asked for.

---

## 6. Delta-scan addendum — one new reuse row

The pre-campaign table (`docs/2026-08-20_iris-lean-delta-scan.md` §4,
rows R1–R13) scored every row against the **channel-logic resume**.
This survey adds one row scored against the **campaign**:

| # | Upstream offers (new since pin) | What we built | Migration | Campaign payoff? |
|---|---|---|---|---|
| **R14** | `ProgramLogic/TotalWeakestPre.lean` + `TotalAdequacy.lean` + `TotalLifting.lean` + `TotalEctxLifting.lean` (#554) | The handler equations' **exact step count** (`stepFnIter 3234`, `BfEquation.lean:121`) and the `FuelMeasure`/`CompletesIn` segments — a total-correctness claim family we carry entirely outside the logic | **L**, and only under §3's rebase | **Deferred, but it is the ONLY carrier that would preserve the equations' termination content** if layer C ever moves to a WP. Scores the pin move against the campaign, not only channel-logic. Not a reason to move the pin earlier — the delta scan's §5 sequencing and §6 [USER] rulings stand. |

Rows R1/R2/R3/R6/R7 remain the highest-value rows overall and remain
channel-logic-facing; nothing this survey found changes their
migration classes.

---

## 7. THE SHORTLIST — what is worth campaign units

### NOW (pre-T1) — all cheap, none touching a gate or a statement

1. **[XS, docs] LINEAGE lines + the `Frame` disambiguation.** Give
   `Sym` (King/Cousot symbolic execution + abstract interpretation;
   `Transitions.v:282` as the ported-project instance of the same
   one-directional soundness shape), `FastEval` (Hoare-style data
   refinement), `Frame/` (Yang–O'Hearn locality + Banerjee–Naumann
   location bijections — already in §5c of its design note, promote to
   the header), and the seam (Verdi ghost refinement; ReLoC/Actris for
   the ghost-carried variant) their doctrine-mandated LINEAGE lines,
   and add the two-line note distinguishing `GoLean.Frame` from Iris's
   `Frame` class. Closes the clever-tricks convention's open items for
   all four campaign mechanisms at once.
2. **[S–M, proofs] A4-U5 takes the `Access`-lens shape, not an Iris
   rebase.** `mem.v:78-84` + goose's generated per-field instances is
   the ecosystem's answer to precisely the address-concrete
   struct-store problem A4-U5 was dispatched against, and it needs no
   Iris. This is the single highest-value *actionable* finding in the
   survey.
3. **[XS, docs] Restate layer C in forward-simulation vocabulary**
   (name `R σ N`; state the round step as
   `R σ N → step → ∃ N', specStep N N' ∧ R σ' N'`). Already implied by
   the A4-U5 directive; doing it makes the post-T1 Iris carry a
   restatement rather than a re-derivation.
4. **[XS, docs] Record the three convergences** so they become reusable
   proof infra rather than folklore: `SubTable T σ.types` ↔
   `GoCoreGS.types` pin (§1); `γF`/`γH` ↔ `heapToMap`/`genHeapInterp`
   (§2); the handler-equation pre/post pair ↔ `wp_dsp_send`'s
   `iProto_own` pair and `take_step_X` (§4). Add R14 to the delta-scan
   table (§6).

### POST-T1

5. **Layer C on Iris ghost state** (auth/frag over `absState`, `inv`
   coupling, `goInvariant_of_wp` exit). Cost **L**. Blocked on layer
   B being WP-shaped, which the pilot verdict refuted at hand-walk
   cost. **Flips to high priority the moment T1's scope acquires
   genuine concurrency** — that is the case Iris is for.
6. **`DeadFrom`/`FreshFrom` → `gen_heap` ownership.** Cost S–M,
   conditional on (5); pure duplication otherwise-unactionable today.
7. **The iris-lean pin move.** Unchanged from the delta scan's
   recommendation and [USER] rulings (§5/§6 there): at the chartered
   slice boundary, matching-not-latest, comparator re-pin
   pre-approved. This survey adds R14 to its payoff column and adds no
   urgency.

### EXPLICIT NON-ACTIONS (recorded so they are not re-proposed)

- **Do not rebase Sym or FastEval onto Iris.** Both are accelerators
  bridged by kernel-checked refinement, outside every statement
  closure; the two Iris-ecosystem attempts at the same idea in this
  checkout are dead code, one of them missing exactly the soundness
  theorem we have. If anything, the traffic here runs the other way:
  `Refine.lean:37` completes what `checker__nobuild.v` started.
- **Do not replace the executable frame theorem.** It is upstream of
  Iris, not duplicative; nothing in either checkout proves a frame
  property for a step relation.
- **Do not adopt Perennial's `go.Semantics` axiomatize-the-data-layer
  strategy.** It buys representation-independence by never committing
  to a representation (`new/golang/defn.v:6`, no instance anywhere),
  which is unavailable to a differentially-validated executable
  interpreter.

---

## 8. What I could NOT verify (honest)

- **`deps/perennial` is a shallow clone** (`.git/shallow` present,
  `git rev-list --count HEAD` = 1, tip `43d4efab`, 2026-07-01). The
  classic Perennial/ReLoC refinement stack (`spec_assert.v`,
  `refinement.v`, `refinement_adequacy.v`) and `src/program_proof/`
  are **not in this snapshot**. Every "Perennial does not have X"
  above means "not in this checkout" and must not be read as a claim
  about upstream Perennial.
- **No local artifact for RefinedC/Lithium or Diaframe.** `ls deps/`
  in this worktree = `go goose iris-lean perennial raft`. I named them
  only as unchecked comparanda; the survey makes no claim about their
  automation beyond that. (The task brief also asked about an
  "iris-papers audit doc in `deps/`" — there is none.)
- **No local artifact for the papers** cited as classics (King 1976;
  Cousot & Cousot 1977; Hoare 1972; Yang & O'Hearn 2002;
  Calcagno–O'Hearn–Yang 2007; Banerjee–Naumann; ReLoC; Simuliris).
  Where a local *doc* records a from-memory citation I cite the doc
  and say so (`docs/2026-08-06_concurrency-research-iris-ecosystem.md:233`,
  `:247`; `docs/2026-08-13_executable-frame-theorem.md:252`).
- **`deps/verdi`, `deps/verdi-raft`, `deps/StructTact` are absent from
  this worktree**, so Arc 3's actual ancestor (Verdi's ghost
  refinement) was not re-read this session; §3's Verdi claims are
  taken from our own design notes.
- **No build was run.** Every claim about our tree is from reading
  source and from `grep`/`wc` counts, not from elaboration. In
  particular the cost classes (S/M/L) are judgments from proof shape
  and from the pilot verdict's measured numbers, **not** measurements
  taken here.
- **iris-lean was read at the pinned rev** `3877dbec` (the reading
  copy's `HEAD`); master-only items (`AbstractWP`, `TotalWeakestPre`,
  `iinv`, later credits) are cited from the delta scan's diff work,
  not re-derived.

---

## Provenance

Read this session, read-only: `proofs/GoLeanProofs/{Sym,FastEval,
Frame,Specs/Raft,StepKit,Ghost,Adequacy,SurfaceExit,Surface,
Tactics/GoWalk}`, `GoLean/GoCore/MachineSound.lean`, `docs/kit-guide.md`,
`docs/2026-08-{13_executable-frame-theorem,20_iris-lean-delta-scan,
22_fasteval-design,22_campaign-arc4-seam-design,
22_campaign-arc4-sym-extension-design,06_concurrency-research-iris-ecosystem}.md`,
`docs/raft-campaign-log.md`, `CLAUDE.md`; `deps/iris-lean` at
`3877dbec`; `deps/perennial` at `43d4efab` (shallow) and `deps/goose`
at `3be88bb`, the latter two partly via two decorrelated read-only
survey agents whose top-line file:line claims (`Transitions.v:282`,
`mem.v:78-84`, `dsp.v:226`, `dsp_ghost_theory.v:303-315`,
`Makefile:4`, and the "`interpret` has no consumers" negative) I
re-verified myself by direct read. No file outside this one was
modified; no build was run.


## Addendum (2026-08-27, [USER] challenge + resolution): why Iris does
not apply at the T1 seam — the atomicity-degeneracy argument

[USER] pressed: the seam is a refinement proof; isn't that Iris's home
ground (logical atomicity)? And the TCB point is irrelevant — prove in
Iris, map down via adequacy. Resolution, recorded:
- **TCB: conceded.** Adequacy + first-order readout corollaries make
  the statement-TCB doctrine a non-blocker; it constrains placement,
  not use.
- **The operative reason: atomicity is DEGENERATE at T1.** Logical
  atomicity / linearization-point machinery exists to place the
  abstract commit inside an execution OTHER threads can observe
  mid-operation; prophecy/step-indexing handle future-dependent or
  circular placement. The T1 twin is closed and sequential: rounds
  run to completion deterministically modulo the explicit quantified
  choice stream; no observer of mid-round states exists; the commit
  point is trivially the round boundary. What remains is a plain
  forward simulation of a sequential transition system — direct
  induction proves it; the Iris route re-derives the same
  first-order statement through ghost coupling + mask bookkeeping +
  adequacy. Two-axis test: fails (cost up, zero additional
  consumers), independent of NIH.
- **Practical asymmetry:** the Iris refinement superstructure
  (Trillium/ReLoC/Perennial simulation-transfer) is Rocq-side;
  iris-lean provides base logic + ProofMode. Porting it is triggered
  by the problem that needs it, per the middle path.
- **The flip condition (standing, explicit):** real concurrency
  (channel-logic resume, goroutine interleaving, the full node
  pipeline) makes mid-operation states observable → linearization
  points become real → Iris becomes the right frame. absState's
  coupling stays rebase-compatible with excl-auth (§3); tripwires:
  the sequential kit sprouting invariant-opening patterns; the
  exact-step equations needing TotalWeakestPre on any carry.
