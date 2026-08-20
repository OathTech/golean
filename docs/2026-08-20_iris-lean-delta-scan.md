# iris-lean upstream delta scan (2026-08-20)

Read-only reconnaissance for the W3.2 charter's **slice 6b** (the iris-lean
refresh & reuse survey,
`docs/2026-08-20_w32-re-envelope-charter.md` §S6b). Runnable pre-arc: this
scan changes nothing — no manifest edit, no pin move, no touch to
`deps/iris-lean`'s working tree (it stays detached at the pinned rev; Mike
fetched upstream refs into it and everything below is read through `git`).

Scope: (1) what upstream gained since our pin, (2) where it could replace
machinery we hand-rolled, (3) what a pin move actually costs. The
recommendation is at the end.

---

## 0. The two revs, cross-checked

| | rev | date | source of truth |
|---|---|---|---|
| **Our pin** | `3877dbeccd1b0545c5be7ef73318e8c86acf79ab` | 2026-06-25 | `proofs/lakefile.toml` `[[require]] name = "iris"` `rev = …`, echoed in `proofs/lake-manifest.json` and (inherited) `compat/gobra/lake-manifest.json` |
| **Upstream head** | `e7a0a43814c4f1154ca0c8049883ca56c2288b86` | 2026-08-19 | `deps/iris-lean` `refs/remotes/origin/master` |

Both manifests agree with the lakefile, and `deps/iris-lean` `HEAD` is
`3877dbe` — the reading copy and the Lake pin are in sync **today**.
`scripts/setup-deps` mechanizes that: the `iris-lean` row's pin is the literal
string `manifest`, resolved out of `proofs/lake-manifest.json`, and the script
fails closed on drift. So "manifest + reading copy move together" is already a
gate, not a convention — the pin-move commit must update the manifest and
re-checkout `deps/iris-lean`, or `setup-deps` goes red.

Pin's tip commit: `feat: port bi/monpred.v (MonPred BI) (#481)`.
Head's tip commit: `feat: Port OwnP (#653)`.

---

## 1. The delta

**135 commits, zero divergence** (`git rev-list --count origin/master..3877dbe`
= 0 — we are a strict ancestor, so this is a fast-forward, not a fork).
**316 files, +40,641 / −11,181.**

### 1a. By area

Commits touch several areas each, so these overlap; the number is "commits
touching this area".

| bucket | commits | net lines (files → dir) |
|---|---:|---|
| algebra / cmra | 55 | `Algebra/` +8,856 / −2,745 (44 files) |
| base logic + BI | 50 | `BI/` +6,016 / −1,486 (41 files) |
| std / support | 39 | `Std/` +1,206 / −398 (31 files) |
| heaplang | 37 | `HeapLang/` +4,957 / −410 (31 files) |
| proofmode / tactics | 36 | `ProofMode/` +5,431 / −1,961 (56 files) |
| instances (invariants, ghost state) | 34 | `Instances/` +2,121 / −354 (21 files) |
| program logic | 24 | `ProgramLogic/` +2,518 / −42 (16 files) |
| build / toolchain / CI | 12 | lakefiles, `scripts/`, workflows |

Tests moved wholesale `Iris/Iris/Tests/` → `Iris/IrisTest/` and grew
(`IrisTest/Tactics.lean` alone is 4,353 lines); the lakefile now declares
`IrisTest` as a `testDriver` rather than a default target.

### 1b. Substance, bucket by bucket

**Proofmode / tactics** — the most consequential bucket for us. New tactics
that did not exist at the pin at all: `iinv` (#470), `iinduction` (#430),
`iaccu` (#487), `ieval` / `isimp` / `iunfold` (#490). Intro-pattern and
case-destruction patterns completed (#496), specialisation patterns completed
(#500), `iframe` with existentials (#511). Error messages routed through
`throwIPMError` (#592), proof-state display reworked (#591), a raft of
instance-priority and synthesis fixes (#555 `AndIntoSep`, #575 `AsFractional`
direction, #594 `isDefEqStuck`, #626 `infer_instance` side conditions, #611
invariant-side-condition recursion depth, #606 elab/delab of propositions,
#541/#573 overlapping-instance removals). A `semiOutParam` attribute for
`ipm_class` (#513); `match` support inside `iprop(…)` (#525); `istart` with an
explicit BI (#505); `simp`/`rw` no longer silently exit the proof mode (#506).

**Algebra / cmra** — dominated by **the setoid retirement** (#502 step 1, #533
the retirement itself, #645 OFE cleanup, #636 "Finish OFE"). Equivalence on
carriers moves from a setoid `≡` discipline toward propositional `=` where the
carrier is extensional. Consequences visible in the diff: `LeibnizO` → `DiscreteO`,
`iOwn_ne.eqv h` → `congrArg (iOwn _) h`, `valid_iff` dropped, `equiv_iff.mp`
often unnecessary. Also: `Agree` rebuilt on the generic quotient (#586), the
Banach fixpoint and the COFE-solver isomorphism made opaque (#498, and the
up/down pair by a single recursion), `algebra/stepindex.v` ported (#515) with
`IrisMath/StepIndex.lean` alongside — the groundwork for generalized step
indices. New ported libraries: `mra`, `coPset`, `gset`, `gset_bij`, `gmultiset`,
`functions`, `ufrac_auth`, `dyn_reservation_map`, `vector`, monotone-list
family, `UFrac`, `cmra_big_op`, `MonoNat` made distinct from `Nat` (#563).
`sts.v` explicitly declined (#635).

**Base logic** — `feat: 100% base_logic` (#656), `Finish base_logic/own.v`
(#634), several files finished (#584), `bupd_alt` annotated (#629). New
`bi/lib/` ports: `core.v` (#522), `relations.v` (#588), `counterexamples.v`
(#540, which also fixed `IntoWand` instances), `laterable.v` + `TCForall`
(#560), `telescopes.v` (#598, plus `Std/Telescopes.lean`). Big-operator work:
`big_sepM2` (#582), `big_opMS`/`big_sepMS` over gmultisets (#495). Derived-law
files brought to completion (#539, #631, #620).

**Later / Löb / step-indexing** — `inext` gained a **later-credits** form
(#510: `inext n credit: H`, `inext credit: H`); its elaboration was made
substantially faster (#633). `laterN` redefined via `Nat.repeat` (#520).
`InstancesLater.lean` reworked (+402/−…) and completed (#650). Löb
(`iloeb`) already existed at the pin; `Loeb.lean` got +82/−… of generalizing
work.

**Invariants** — the pin's `Invariants.lean` carried a literal
`-- TODO: into_inv_inv, into_acc_inv`. Master ships both `IntoInv` and
`IntoAcc` instances for `inv N P`, which is precisely what makes the new
`iinv` tactic work on an ordinary invariant. `inv_alloc` / `inv_acc`
statements are unchanged. Cancellable and non-atomic invariants extended,
`WSat` and `FUpd` grown (+161 on FUpd).

**Ghost state** — four genuinely new modules under `Instances/Lib/`:
`SavedProp.lean` (#503, saved propositions — higher-order ghost predicates),
`Boxes.lean` (#466, Iris "boxes": the canonical slot/resource-transfer
construction), `GhostVar.lean` (#619), `SetBij.lean` (#579, `gset_bij`).
`GhostMap` reworked; `GenHeap` annotated and `InvHeap` ported (#618);
`heapview` annotated (#655).

**Program logic** — the biggest *structural* additions, all new files:
`AbstractWeakestPre.lean` (#475: an `AbstractWP` abbreviation plus
`LawfulAbstractWP` / `BindAbstractWP` / `InvOpenAbstractWP` classes — WP laws
stated once against an interface rather than against a concrete `wp`),
`AbstractLangCompleteness.lean` + `AbstractEctxLangCompleteness.lean` (#476,
#474), `TotalWeakestPre.lean` + `TotalAdequacy.lean` + `TotalLifting.lean` +
`TotalEctxLifting.lean` (#554, total/terminating WP), `ThreadPool.lean`
(multi-thread `PrimSteps`, `cfgNotStuck`, `cfgForking`), `OwnP.lean` (#653).
The existing `WeakestPre.lean` grew `AddModal`, `ElimAcc` (atomic and
non-atomic) and `ElimModal` instances where the pin had only a
`TODO: AddModal, ElimAcc instances` comment.

**HeapLang** — went from 14 files to 31: metatheory (#607), pure-step tactics
(#516), heap tactics (#521), `Completeness.lean`, `DerivedLaws.lean`,
`Tactic.lean` grown, a Texan-triple syntax (#484) later made persistent
(#568), and a library (ticket lock, rw lock/spinlock, counter, assert, array,
arith, diverge, unwrap, clairvoyant coin, lazy coin, nondet bool) with all
locks moved to texan triples (#642).

**Build / toolchain** — see §3; the short version is Lean **v4.31.0 →
v4.32.2** and batteries/Qq **v4.31.0 → v4.32.0**, plus a benchmark suite
(#512), a `check-imports` Lean exe and CI step (#589), and porting-script
fixes (#622, #644).

---

## 2. Breaking changes, checked against what we actually use

Method: enumerate every `import Iris…` in `proofs/` and `compat/` (excluding
`.lake/`), extract the Iris identifiers our files name, and compare each
declaration's statement at `3877dbe` vs `origin/master`.

Our direct Iris surface is **19 files** out of 259 in `proofs/`
(`Adequacy`, `Ghost`, `HeapBridge`, `Lang`, `LangC`, `LangD`, `Lifting`,
`SurfaceExit`, `Tactics/GoWalk`, `Specs/GoldenSliceWP`, and the nine
`Laws/*`). `compat/gobra` and `compat/verdi` contain **no** Iris imports —
`compat/gobra` only inherits the dependency transitively through
`golean-proofs`, and `GobraCompat/Contract.lean` states in prose that its
elaboration target is the Iris-free Surface layer.

Every module path we import still exists at master (all 23 checked: `OK`).

### 2a. Verified unchanged (statement-identical at both revs)

- `genHeapInterp`, `genHeap_valid`, `genHeap_alloc`, `genHeap_update`,
  `genHeap_init_names`, `genHeapInterp_eqv`, `genHeapGS`, `genHeapPreS` —
  all five theorem statements byte-compatible; only proofs and internals
  moved (`LeibnizO` → `DiscreteO` inside `MetaUR`).
- `fupd_intro`, `fupd_mask_intro`, `fupd_mask_intro_discard` — identical
  (this matters: `fupd_intro` appears **393** times in our proofs).
- `LawfulPartialMap.get?_empty` / `get?_insert_eq` / `get?_insert_ne` /
  `get?_delete_*` — field-for-field identical. These are the only
  `PartialMap` lemmas we name.
- `inv_alloc`, `inv_acc` — unchanged.
- `≡ₘ` notation survives (we have 5 uses, all in `HeapBridge`/`SurfaceBridge`,
  all consumed by `genHeapInterp_eqv`, which still takes `≡ₘ`).
- `inext` bare form unchanged; the credits form is purely additive.
- `ExtTreeMap K · compare` still gets `PartialMap`, `LawfulPartialMap`,
  `FiniteMap`, `LawfulFiniteMap`, `UnboundedHeap` (relocated within
  `Std/HeapInstances.lean`) — our `GoHeapF` keeps its instances.

### 2b. Real breaks, ranked

1. **Toolchain: Lean v4.31.0 → v4.32.2** (and batteries/Qq → v4.32.0).
   Not optional — `Iris/lean-toolchain` at master is v4.32.2, and Lake
   requires the packages to agree. This is a **whole-repo** bump: our four
   `lean-toolchain` files (`./`, `proofs/`, `compat/gobra/`, `compat/verdi/`)
   over ~28k lines of GoLean core, ~168k lines of proofs, ~4k of compat.
   Mitigations: v4.32.2 (and v4.33.0) are already installed under
   `~/.elan/toolchains`, so nothing is downloaded; and the module system
   (`module` / `public import`) is already in use at *both* revs, so that
   migration is not part of this delta.
2. **`ElimModal` gained a parameter.** Pin:
   `ElimModal (φ) (p) (p' : outParam Bool) …`. Master:
   `ElimModal (φ) (p) (io : InOut) …`. Every `ElimModal` instance in the
   ecosystem is restated. **We declare none** (`grep` = 0 in `proofs/`), so
   this bites only if the pin move is combined with new modality work.
3. **`IrisGS_gen` restructured.** Pin: `extends StateInterp …, InvGS_gen hlc GF`.
   Master: `extends StateInterp …` with `[invGS : InvGS_gen hlc GF]` as an
   instance-implicit *field* (plus `attribute [implicit_reducible, instance]`).
   We construct three `IrisGS_gen` instances (`Ghost.lean:77`, `LangC.lean:125`,
   `LangD.lean:636`), each supplying only `numLatersPerStep` / `forkPost` /
   `stateInterp_mono` — those should keep elaborating (the new field is
   synthesized from our `GoCoreGS.toInvGS_gen`), but the parent projection
   `IrisGS_gen.toInvGS_gen` is gone. **Verify by building, do not assume.**
4. **Setoid retirement, spillover.** `LeibnizO` → `DiscreteO`;
   `ExtensionalPartialMap` and `IsoFunMap` classes removed;
   `iOwn_ne.eqv h` → `congrArg (iOwn _) h`; `valid_iff` gone; a family of
   `PartialMap` lemmas now conclude `=` where they concluded `≡ₘ`
   (`union_empty_left/right`, `map_empty`, `delete_empty`, `delete_of_get?`,
   `eq_empty_iff`, `insert_ne_empty`, `singleton_ne_empty`,
   `delete_singleton_eq`, `map_equiv`). We name **none** of these, and use
   none of the removed classes — but our `HeapBridge` extensionality
   lemmas (`insert_eqv`, `heapToMap_set_base₂/₃`) are hand proofs of exactly
   what `equiv_iff_eq` now gives for free upstream.
5. **`Iris.Std.AssocList` deleted** from `Std/HeapInstances.lean` (with its
   `PartialMap`/`Heap`/`UnboundedHeap` instances). Zero uses in our tree —
   noted only because a future heap-representation change might have reached
   for it.
6. **Tactic-syntax rename `in` → `at`** (#585) for `ieval` / `isimp` /
   `iunfold`. Harmless for us: all three are *new* since the pin, and our
   entire Iris tactic vocabulary is `iapply` (1043), `iintro` (578),
   `isplitl` (279), `iexact` (261), `inext` (217), `ipureintro` (100),
   `icases` (61), `iexists` (57), `imod` (53), `imodintro` (38), `ihave` (37),
   `iframe` (26), `isplitr` (23), `isplit`/`ileft`/`iright` (1 each) — none
   of which changed syntax.
7. **The silent class: instance priorities and synthesis.** Seven upstream
   fixes change *which* instance fires for `iframe` / `isplit` / `iapply` /
   `icombine` (#555, #575, #573, #541, #594, #626, #611, plus the new
   `frame_pointsto`, `CombineSepGives`/`CombineSepAs` points-to instances and
   `FrameInstantiateExistDisabled`). This will not appear as a rename; it
   appears as a proof that used to close and now doesn't, or vice-versa. In a
   167k-line proof tree with a `go_walk` tactic that leans on synthesis, this
   is where the pin-move hours will actually go — **budget for it explicitly**.

**Not a break, worth flagging:** upstream has an unmerged `bump-4.33.0` branch
(1 commit ahead of an older master, 55 behind). A 4.33 bump is in flight, so a
pin landed on today's master is likely to be superseded within weeks. That
argues for pinning once, deliberately, at a slice boundary — not for chasing.

---

## 3. Pin-move cost

**Files carrying the pin (all must move in the one gated commit):**

- `proofs/lakefile.toml` — the authoritative `rev = "3877dbe…"`.
- `proofs/lake-manifest.json` — regenerated.
- `compat/gobra/lake-manifest.json` — inherits `iris` transitively; regenerated.
- `deps/iris-lean` working tree — re-checkout to the new rev
  (`scripts/setup-deps` reads the manifest and fails closed otherwise).
- `./lean-toolchain`, `proofs/lean-toolchain`, `compat/gobra/lean-toolchain`,
  `compat/verdi/lean-toolchain` — v4.31.0 → v4.32.2.

**`compat/` — barely cares, and that is by design.** Neither `compat/gobra`
nor `compat/verdi` imports Iris; both are isolation-contract packages
referenced by nothing in the main build. Their cost is the toolchain bump
alone (3,829 lines total).

**The comparator area — cares a lot, and it is the sharp edge.** The judged
trust surface is safe: `proofs/Challenge.lean`'s import closure is
**Iris-free by construction**, enforced twice (`scripts/ci`'s surface-purity
scan and `comparator-judge` §3c's module-level walk), so no pin can change
what a judged statement says. But the *replay mechanism* is version-locked:

- `deps/comparator` is pinned at `fd2e25d` with `lean-toolchain` =
  **leanprover/lean4:v4.31.0**, and `deps/comparator/.lake/packages/lean4export`
  at `8554815`. `comparator-judge` refuses to run unless both are at their
  pins **and pristine**.
- The judge runs `lake env <comparator> judge-config.json` inside `proofs/`
  with `COMPARATOR_LEAN4EXPORT` pointing at that 4.31-built binary. Move our
  toolchain to 4.32.2 and a 4.31 exporter is asked to read 4.32 artifacts.

So the pin move very likely **forces a comparator + lean4export re-pin**, and
those are trust tools: never modified, re-pinned only with explicit user
approval at the moment of execution. Treat "does the judge still run" as a
**precondition to plan for**, not a surprise to discover — and note that the
judge is landmark-cadence, so it will not fail in `scripts/ci` and warn you.

**Our own bill:** 19 direct-importer files to fix mechanically, plus an
unknown tail from §2b item 7 across the 240 files that reach Iris
transitively. The channel-logic lane (parked, `../channel-logic`) carries the
same pin in its own `proofs/lake-manifest.json` — it must be rebased through
the pin move, not merged across it.

---

## 4. Reuse candidates (draft table)

The channel-logic lane is the heavy consumer; its Iris-shaped components are
`chanInv`/`chanInvP` (an `inv`-pinned channel cell with a `[∗list]` per-element
predicate — pure tier `Ψp : GoValue → Prop`, resource tier
`Ψ : GoValue → IProp`), the `wpDM` mediated weakest precondition over
`LangDM`/`LangD`/`LangC` thread-pool carriers, the `LawsDM` port of the
sequential law family onto that carrier, the meta-token identity tie
(`meta_set` / `meta_agree` over `genHeap`'s meta machinery with local
`Pos.Countable` instances), and the `GoTripleC` / `dspCompTripleC`
frame-quantified triple shape. Its measured Iris API usage is small and
entirely in the "verified unchanged" set of §2a: `genHeap_*` (46),
`metaToken`/`metaInfo`/`meta_set`/`meta_agree` (30), `inv_alloc`/`inv_acc` (18).

| # | Upstream offers (new since pin) | What we built | Migration | Cheaper channel-logic resume? |
|---|---|---|---|---|
| R1 | `AddModal` + `ElimAcc` (atomic & non-atomic) + `ElimModal` instances for `WP` (`ProgramLogic/WeakestPre.lean`; the pin had `TODO: AddModal, ElimAcc instances`) | The **modality dance**: `iapply fupd_intro; inext; iapply fupd_intro; iintro -`, as `go_walk_dance` in `Tactics/GoWalk.lean:276` and as a `local macro "idance"` twice (`Laws/Slice.lean:145`, `Examples/Fib.lean:252`). 393 `fupd_intro` sites. | **M** — mechanical but wide; the tactic core changes once, the call sites shrink | **Yes.** Every `wpDM` law ends in the same dance |
| R2 | `iinv` tactic (#470) + `IntoInv`/`IntoAcc` instances for `inv N P` | 12 hand-rolled `inv_acc` open/close blocks with manual mask side-conditions in `ChanD`/`ChanDM`/`ChanDMRes` | **S–M** — per-site, and the mask obligations become instance-discharged | **Yes.** This is the channel logic's most repeated idiom |
| R3 | `AbstractWP` + `LawfulAbstractWP` / `BindAbstractWP` / `InvOpenAbstractWP` (#475), with `AbstractLangCompleteness` / `AbstractEctxLangCompleteness` | `wpDM` and the `LawsDM` re-port: the sequential `Laws/*` family **restated** on the mediated carrier because the laws were tied to a concrete `wp` | **L** — a genuine restructuring, and the highest-value one: state the law family once against the interface, instantiate per carrier | **Yes, structurally.** It is the direct answer to "S2 note §6 obstacle 2" |
| R4 | `ProgramLogic/ThreadPool.lean` (`PrimSteps`, `cfgNotStuck`, `cfgForking`, `Forking`) | The pool-carrier plumbing hand-built across `LangC` / `LangD` / `LangDM` (2,490 lines in `LangDM` alone) | **L**, and **assess before adopting** — ours is shaped by GoCore's `execProg` and the doctrine's latitude; upstream's is HeapLang-shaped | **Partly.** Likely *keep ours* for the carrier, *reuse* the safety/forking predicates |
| R5 | `Instances/Lib/Boxes.lean` (#466) + `SavedProp.lean` (#503) | `chanInv`'s `[∗list]`-over-buffer resource tier, with the **timeless restriction** on `Ψ` recorded as park item P-CL3-3 | **M** | **Yes** — boxes are the canonical Iris resource-transfer slot construction, and saved props are how a higher-order `Ψ` stops needing timelessness |
| R6 | Later credits: `inext n credit: H` (#510), `LaterCredits` grown | The timeless-`Ψ` workaround itself: opening the invariant yields `▷ chanInv` and the proofs strip the later by timelessness | **M** | **Yes, and it retires a parked item.** P-CL3-3 ("later-credit generalization for genuinely higher-order Ψ") is *exactly* this feature |
| R7 | `iinduction` (#430) + `iloeb … generalizing!` work (#…, `Loeb.lean` +82) | The parked-law Löb inductions in `ChanD`, hand-driven; and the S3 blocker: "loop-invariant machinery, loop NOT unrollable — unbounded service loop re-parks per request" | **M** | **Yes** — this is named in the park record as the missing machinery for the client-side loop |
| R8 | `Instances/Lib/SetBij.lean` (`gset_bij`, #579), `GhostVar.lean` (#619) | The meta-tie: `meta_set` on a `makeChan` token + `meta_agree` at receive, with local `Pos.Countable Nat`/`Addr` instances (FD9) | **S** | **Marginal.** Ours works and is small; `SetBij` is the more principled two-sided name tie if the tie ever needs to be symmetric |
| R9 | Texan triple syntax (#484), made persistent (#568); `bi/telescopes.v` + `Std/Telescopes.lean` (#598); all upstream locks moved to texan triples (#642) | `GoTripleC` / `dspCompTripleC` — frame-quantified triples over a pinned lowering | **M** | **Maybe.** Telescoped texan triples are the standard binder story; adopt only if our triple's frame-quantification maps onto it cleanly |
| R10 | `TotalWeakestPre.lean` + `TotalAdequacy` + `TotalLifting` (#554) | `Specs/TotalPins.lean` (436 lines) — our total-correctness pins | **M–L** | Not channel-logic, but it is the upstream home for a claim family we currently carry alone |
| R11 | HeapLang pure-step tactics (#516), heap tactics (#521), `HeapLang/Tactic.lean` grown, `wp_pures` guard fix (#604), `wp_store`/`wp_xchg` auto-sequence (#600) | `go_walk` / `go_walk_step` / `go_walk_finish` / `go_walk1` + the `@[go_walk_law]` `DiscrTree` (`Tactics/GoWalk.lean`, 603 lines) | **keep ours** — upstream's are HeapLang-specific, and `go_walk`'s law table is the structural over-specialization guard (the file *cannot* name quorum) | Indirectly: read them for technique, don't import |
| R12 | `equiv_iff_eq` (extensional maps, #488) | `HeapBridge.insert_eqv`, `heapToMap_set_base₂/₃` — hand extensionality congruences | **S** | Minor, but it is free cleanup landing with the bump |
| R13 | `HeapLang/Lib/{SpinLock,TicketLock,RwLock,Par,Spawn,Counter}` on texan triples | `Specs/ForkJoinTargets`, `GoldenForkJoin`, `SpawnNoopProgress` | **keep ours** — these are *Go's* fork/join, differentially anchored, not HeapLang's | No |

**Keep-ours rows, with the reason stated (the DONE criterion for S6b's table):**
R4 (carrier shaped by GoCore + the latitude doctrine, not by HeapLang), R11
(`go_walk`'s language-agnostic law table is a deliberate over-specialization
guard), R13 (the fork/join specs are differentially anchored Go, and swapping
them for HeapLang analogues would be exactly the over-specialization drift the
audit doctrine names). R8 is a *lean*-keep-ours: ours is smaller and works.

---

## 5. Recommendation

**Move the pin in W3.2 slice 6b, as chartered. Not earlier.**

Reasons, in order:

1. **The fast-forward is clean but the toolchain is not free.** 135 commits,
   zero divergence, and every identifier we actually name is statement-identical
   (§2a). The cost is not the Iris API — it is the Lean v4.31.0 → v4.32.2 bump
   across ~200k lines and the instance-priority tail (§2b item 7). That is a
   dedicated, gated commit, which is exactly what S6b already specifies.
2. **Doing it earlier buys nothing and costs the arc.** Every reuse candidate
   in §4 pays off in the **channel-logic resume**, which S6c only *assesses*;
   none of them accelerate slices 0–5 (the re-envelope work is machine-side,
   not proof-side). Moving the pin mid-arc would put a toolchain bump under
   unrelated semantics surgery.
3. **Staying is not viable much longer.** Six of the ten reuse rows retire
   things the channel-logic park record explicitly lists as blockers or parked
   items — R1/R2 (repeated idioms), R3 (the `LawsDM` re-port obstacle), R6
   (P-CL3-3 verbatim), R7 (the loop-invariant blocker). The resume is
   materially cheaper *after* the pin move, so the pin move should precede the
   resume — and S6b already sits before it.
4. **Sequence inside S6b:** (a) pin move + toolchain bump as its own commit,
   with the comparator/lean4export re-pin question **raised for approval
   before** it starts, not discovered during it (§3); (b) the reuse table
   above, promoted from draft once the build has confirmed items 2b-3 and
   2b-7 empirically; (c) leave the actual migrations (R1–R7) to the resume
   charter — S6b's DONE is "pin moved green in its own commit; table exists
   with a reason on every keep-ours row", not "machinery replaced".

**One caveat to carry:** upstream's `bump-4.33.0` branch is in flight. Pin at
a rev chosen deliberately at the slice boundary and record it; do not chase
master afterwards.

---

## 6. USER RULINGS (2026-08-20, Mike)

- **The recommendation is ADOPTED**: the iris-lean pin moves in W3.2
  slice 6b as chartered — not earlier; every reuse row pays off at the
  channel-logic resume, and a toolchain bump does not belong under
  semantics surgery.
- **The comparator re-pin is PRE-APPROVED**: at the slice-6b boundary,
  `deps/comparator`'s `lean-toolchain` and its `lean4export` build
  move to MATCH the main proof toolchain (4.32.2 at the boundary —
  matching, not "latest", is the rule: the judge replays what the
  kernel checks, so the versions must be identical; today they
  coincide). Conditions per the trust-tools rule: a version move
  only — comparator/lean4export sources stay pristine; the re-pin
  commit records old→new + rebuild provenance; the judge re-runs on
  a known-good landmark as the post-move check.

## Provenance

Everything above was read from `deps/iris-lean` via `git` at
`origin/master` = `e7a0a43` and the pin `3877dbe`, and from the
`w32-charter` worktree at `b4c6ef55`. No file in `deps/iris-lean` was
modified; its `HEAD` remains detached at the pinned rev. Line and file counts
are `git diff --numstat` / `wc -l` outputs; identifier counts are `grep -o`
tallies over `proofs/` excluding `.lake/`.
