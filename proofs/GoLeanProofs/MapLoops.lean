import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure

/-!
# The map-loop schemas (Gallery Campaign kit-gap closure, 2026-08-15)

The two loop-composition schemas the map-counting examples share,
lifted out of `Examples/WordCount/CountGeneric.lean` (GAP-C1) and —
in the second section — the choice-pick loop induction of
`Examples/WordCount/RangeGeneric.lean` / histogram's `hg_range_loop`
(GAP-R1):

* **The counting loop** (`m[k]++` folded over a slice):
  `mapCountIter_generic` (one 53-step iteration) and
  `mapCountLoop_generic` (the strong induction over the remaining
  count, back-edge included, ending at the exit test's `false`
  delivery). Both were already stated placement-generically in
  wordcount's `CountGeneric` shard — over the state family, the
  placement environments/continuations and per-segment facts — but
  over CONCRETE statement constants embedding the Go slice name
  (`"words"`), so histogram (`"vals"`) re-derived the whole tower.
  Here the body's statements are parameterized by the one name they
  embed (`slVar`); everything else about the desugared `m[k]++` body
  (`$c1`/`$c2` temps, the `counts` local, the `mapAssign` spine) is
  the frontend's fixed shape and stays concrete.
* **The counting-loop EXIT is deliberately NOT here**: wordcount's
  exit allocates and snapshots (23 steps), histogram's does neither
  (9 steps) — the honest shared part ends at
  `.retV (.bool false) cmp`, and each consumer chains its own exit
  (the same boundary call the P5 setup-loop schema made).

## The storm discipline

**StepKit rules 1–5** (that module's `## THE FIVE RULES` section is
the kit's single copy — cite, never restate). Concretely, as they
land here: every hypothesis type pins all intermediate states and
configurations, so no instantiation can send the unifier into a
concrete heap front (rules 1–2, the 2026-08-13 storm diagnosis); at
instantiation sites that mention big concrete states, pin the full
result type on the `have` (rule 3, the E-form).

## PUBLIC API — the sealed interface (the W6 convention, as in
`StepKit`/`MapMem`)

**What consumers may depend on** (and nothing else). The groups are
indexed by PROOF SITUATION (the WP arc s3 convention); the in-file
`/-! ## … -/` section headers carry the group number.

**Group 1** — *you are naming the desugared `m[k]++` loop body*: the
statement vocabulary `mhG`, `wsHG`, `asgnC1G`, `asgnReadG`,
`seqnC2G`, `mapAsgnG`, each parameterized over the identifier strings
the frontend embeds (`slVar`/`mapVar`/`c1`/`c2`/`iVar` — GAP-C1b, WP
arc s2 item 7), with the spelling helpers `tU64`, `tMap`, `u64cell`.

**Group 2** — *your program counts into a map over a slice, and you
need the LOOP* (GAP-C1): `mapCountIter_generic` (one iteration, 53
steps, placement-generic) and `mapCountLoop_generic` (the strong
induction over the remaining count, back-edge included, ending at the
exit test's `false` delivery).

**Group 3** — *you are placing that loop in a CONCRETE example*:
`mapCountIter_at`, the bundled per-placement form — placement facts +
raw segments in, conditioned discharges constructed inside.

**Group 4** — *your program RANGES over a map and you need the pick
loop* (GAP-R1): `mapPickLoop_generic`, with the list-consumption
helpers it is stated against — `consume_lt`, `eraseIdx_length_of_lt`,
`mem_of_mem_eraseIdx`.

**Internal** (`private` — spelling may change without notice):
`defaultValue_tMap`, `defaultValue_tU64`, `normMapHandle`, `normU64`
— the per-placement discharge steps of `mapCountIter_at`.

**The API discipline**:

1. Everything here is UNTRUSTED METHOD (proof-side): no name from
   this module may appear in a headline statement closure (§12b).
2. Additions follow the §12 active-abstraction loop (≥2 consumers
   retrofitted in the lifting commit, measured deltas).
3. The seal is name-level + this contract; `private` hides names
   without sealing definitional transparency.
4. Every public THEOREM above carries an exact `#print axioms` pin in
   `Audit/Kit.lean` § MapLoops; the statement-vocabulary `abbrev`s
   are unpinned by the standing convention.
5. **Storm/signature discipline: StepKit rules 1–5** — see the
   section above for how they land in these schemas.

**Naming note** (WP arc s3): `_generic` marks the placement- and
name-generic SCHEMA; `_at` marks the bundled at-a-placement form
built from it. That pair is the kit's convention for any future loop
schema, and a `G` suffix marks a statement-vocabulary `abbrev`
(`mhG`, `asgnC1G`, …) as generic in its embedded names.

## WHAT LIVES WHERE (the kit map — WP arc s3, 2026-08-18)

THIS module: whole map-LOOP schemas — the counting loop and the range
pick loop, with their statement vocabulary. It is the composition
layer; it proves no new fact about a map or a step.

Siblings, and the boundary with each:

* `MapMem` — the map facts these schemas consume (`applyStrictOp_
  mapGet`, `mapAssignValue_toEntries`, `stepFn_pick_bind`, the
  `cnt`/`setk` model the invariants are stated in). Anything true of
  a map independent of a loop belongs there.
* `StepKit` — the individual conditioned steps the segments are
  built from.
* `FuelMeasure` — the GENERAL loop schemas (`stepFnIter_iterate`,
  `stepFnIter_iterate_bail`) and the chaining. These map schemas are
  map-SPECIFIC and could not be stated there; a loop shape with no
  map in it belongs there, not here.
* `SliceMem` — the slice side of the counting loop's input.
* The **counting-loop EXIT is deliberately in neither** (see above):
  wordcount's exit allocates and snapshots, histogram's does not, so
  each consumer chains its own.

`docs/kit-guide.md` — THE SITUATION INDEX; read it before writing a
new proof. Sections fed by this module: **Map count loop** (incl. the
five identifier parameters `slVar`/`mapVar`/`c1`/`c2`/`iVar` a
consumer must supply), **Map range loop**.
-/

namespace GoLean.MapLoops

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-! ## API group 1 — the counting-loop statement vocabulary

The frontend's desugaring of `m[k]++` over `slVar[i]` — fixed shape,
one embedded name. -/

abbrev tU64 : Ty := .int .uint64
abbrev tMap : Ty := .map tU64 tU64
abbrev u64cell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩

/-- The map-handle heap cell at data address `bMap`. -/
abbrev mhG (bMap : Nat) : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨bMap⟩)⟩⟩
/-- The input-slice handle over backing address `bArr`. -/
abbrev wsHG (bArr L : Nat) : GoValue :=
  .slice ⟨some (.base ⟨bArr⟩), 0, L, L⟩

/-- `$c1 = counts` (both consumers name the map local `counts` — the
frontend's temp for the map operand). -/
abbrev asgnC1G (mapVar c1 : String) : Stmt := .assign (.var c1) (.var mapVar)
/-- `$c2 = slVar[i]` — the ONE statement that embeds the input slice's
Go name. -/
abbrev asgnReadG (slVar c2 iVar : String) : Stmt :=
  .assign (.var c2) (.indexGet (.var slVar) (.var iVar))
/-- The `$c2` declaration + read, as the frontend splices it. -/
abbrev seqnC2G (slVar c2 iVar : String) : Stmt :=
  .seqn #[.initialization { id := c2, typ := tU64 },
    asgnReadG slVar c2 iVar]
/-- The `mapAssign` spine of `counts[$c2]++`. -/
abbrev mapAsgnG (c1 c2 : String) : Stmt :=
  .mapAssign (.var c1) (.var c2)
    (.add (.mapGet (.var c1) (.var c2) tU64 tU64) (.intLit 1 .uint64))
    tU64 tU64

/-! ## API group 2 — the map-counting LOOP (GAP-C1) -/

/-- **The placement- and name-generic counting ITERATION** (53 steps):
stated over an abstract state family `S`, abstract placement
environments/continuations, the body's embedded slice name `slVar`,
and the per-segment transition FACTS as hypotheses — each hypothesis
type pins every intermediate state and configuration, so no
instantiation can send the unifier into the concrete front (the
storm-class fix). Lifted from `wcIter_generic` (GAP-C1): the only
change of content is that the three body statements are the
`slVar`-parameterized forms above. -/
theorem mapCountIter_generic (slVar mapVar c1 c2 iVar : String)
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp postK : Cont)
    (env3g : LocalEnv) (u1Envg uEnvg : Nat → LocalEnv)
    -- the segment facts
    (hC1 : ∀ kvs iv dead na ch,
      stepFnIter 7 (S kvs iv false dead na) (.retV (.bool true) cmp) ch
        = .ok (.exec (.initialization { id := c1, typ := tMap }) env3g
            (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] env3g postK),
          S kvs iv false dead na, ch))
    (hInit1 : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := c1, typ := tMap }) env3g
            (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] env3g postK)) ch
        = .ok (.next (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na)
              postK),
          S kvs iv false (dead ++ [(Loc.base ⟨na⟩, nilMapCell)]) (na + 1), ch))
    (hC2 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀)
            postK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
              [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt1 : ∀ kvs iv dead na₀ na ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)),
          S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) na, ch))
    (hC3 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK))) ch
        = .ok (.exec (.initialization { id := c2, typ := tU64 })
              (u1Envg na₀)
              (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK),
          S kvs iv false dead na, ch))
    (hInit2 : ∀ kvs iv dead na₀ ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) (na₀ + 1))
          (.exec (.initialization { id := c2, typ := tU64 }) (u1Envg na₀)
            (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)) ch
        = .ok (.next (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (uEnvg na₀) postK),
          S kvs iv false
            (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch))
    (hC4 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 8 (S kvs iv false dead na)
          (.next (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (uEnvg na₀) postK)) ch
        = .ok (.retV (.int iv .int)
              (.strictK .indexGet [wsHG bArr ws.length] [] (uEnvg na₀)
                (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                  (.seqn #[]) (uEnvg na₀)
                  (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))),
          S kvs iv false dead na, ch))
    (hRead : ∀ kvs (i : Nat) dead na, i < ws.length →
      applyStrictOp (S kvs ((i : Nat) : Int) false dead na) .indexGet
          [wsHG bArr ws.length, .int ((i : Nat) : Int) .int]
        = .ok (.int (ws.getD i 0) .uint64,
            S kvs ((i : Nat) : Int) false dead na))
    (hC5 : ∀ kvs iv dead na₀ na (w : GoValue) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
            (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
              (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt2 : ∀ kvs iv dead na₀ na (w : Int) ch, 0 ≤ w → w < 2 ^ 64 →
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell 0)])
          na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK)),
          S kvs iv false
            (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch))
    (hC6 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 4 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c1) (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 []
                [.var c2,
                 .add (.mapGet (.var c1) (.var c2) tU64 tU64)
                   (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hVar1 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var c1) (uEnvg na₀) k) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩) k,
            S kvs iv false
              (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hVar2 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var c2) (uEnvg na₀) k) ch
        = .ok (.retV (.int w .uint64) k,
            S kvs iv false
              (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hC7 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.stmtOpK (.mapAssign tU64 tU64) 0 []
              [.var c2,
               .add (.mapGet (.var c1) (.var c2) tU64 tU64)
                 (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c2) (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
                [.add (.mapGet (.var c1) (.var c2) tU64 tU64)
                  (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC8 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int w .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
              [.add (.mapGet (.var c1) (.var c2) tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c1) (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [] [.var c2] (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hC9 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.strictK (.mapGet tU64 tU64) [] [.var c2] (uEnvg na₀)
              (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                (.stmtOpK (.mapAssign tU64 tU64) 0
                  [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                  (uEnvg na₀) (.seq [] (uEnvg na₀) postK))))) ch
        = .ok (.evalE (.var c2) (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hMapGet : ∀ kvs iv dead na (w : Int), 0 ≤ w → w < 2 ^ 64 →
      applyStrictOp (S kvs iv false dead na) (.mapGet tU64 tU64)
          [.map ⟨some (.base ⟨bMap⟩)⟩, .int w .uint64]
        = .ok (.int (cnt kvs w : Int) .uint64, S kvs iv false dead na))
    (hC10 : ∀ kvs iv dead na₀ na (w cv : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int cv .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))) ch
        = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hMapAsgn : ∀ kvs iv dead na₀ na (w : Int) (v : Nat) ch,
      0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
      stepFn (S kvs iv false dead na)
          (.retV (.int ((v : Nat) : Int) .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0
              [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.next (.seq [] (uEnvg na₀) postK),
            S (setk kvs w v) iv false dead na, ch))
    (hC11 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.next (.seq [] (uEnvg na₀) postK)) ch
        = .ok (head, S kvs iv false dead na, ch))
    -- the iteration-level hypotheses
    (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat)
    (ch : Choices)
    (hi : i < ws.length)
    (hw0 : 0 ≤ ws.getD i 0) (hw64 : ws.getD i 0 < 2 ^ 64)
    (hcnt : cnt kvs (ws.getD i 0) + 1 < 2 ^ 64)
    (hna : base0 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53 (S kvs ((i : Nat) : Int) false dead na)
        (.retV (.bool true) cmp) ch
      = .ok (head,
          S (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1))
            ((i : Nat) : Int) false
            (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have h1 := stepFnIter_chain (hC1 kvs ((i : Nat) : Int) dead na ch)
    (stepFnIter_one (hInit1 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h2 := stepFnIter_chain h1
    (hC2 kvs ((i : Nat) : Int) (dead ++ [(Loc.base ⟨na⟩, nilMapCell)]) na
      (na + 1) ch)
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (hSt1 kvs ((i : Nat) : Int) dead na (na + 1) ch hna hdead))
  have h4 := stepFnIter_chain h3
    (hC3 kvs ((i : Nat) : Int) (dead ++ [(Loc.base ⟨na⟩, mhG bMap)]) na (na + 1)
      ch)
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (hInit2 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h6 := stepFnIter_chain h5
    (hC4 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) ch)
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_strict_apply (done := [wsHG bArr ws.length])
      (hRead kvs i
        (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell 0)])
        (na + 2) hi)))
  have h8 := stepFnIter_chain h7
    (hC5 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) (.int (ws.getD i 0) .uint64) ch)
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (hSt2 kvs ((i : Nat) : Int) dead na (na + 2) (ws.getD i 0)
      ch hw0 hw64 hna hdead))
  have h10 := stepFnIter_chain h9
    (hC6 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) ch)
  have h11 := stepFnIter_chain h10
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2)
      _ ch hna hdead))
  have h12 := stepFnIter_chain h11
    (hC7 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) ch)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2)
      _ ch hna hdead))
  have h14 := stepFnIter_chain h13
    (hC8 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) ch)
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2)
      _ ch hna hdead))
  have h16 := stepFnIter_chain h15
    (hC9 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) ch)
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2)
      _ ch hna hdead))
  have h18 := stepFnIter_chain h17
    (stepFnIter_one (stepFn_strict_apply
      (done := [.map ⟨some (.base ⟨bMap⟩)⟩])
      (hMapGet kvs ((i : Nat) : Int)
        (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
        (na + 2) (ws.getD i 0) hw0 hw64)))
  have h19 := stepFnIter_chain h18
    (hC10 kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) ((cnt kvs (ws.getD i 0) : Nat) : Int) ch)
  have hcast : ((cnt kvs (ws.getD i 0) : Nat) : Int) + 1
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by omega
  have hnorm1 : IntKind.normalize .uint64 ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int)
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by
    refine GoLean.SliceMem.unorm_of_range (by omega) ?_
    exact_mod_cast hcnt
  rw [hcast, hnorm1] at h19
  have h20 := stepFnIter_chain h19
    (stepFnIter_one (hMapAsgn kvs ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1) ch hw0 hw64 hcnt))
  have h21 := stepFnIter_chain h20
    (hC11 (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1)) ((i : Nat) : Int)
      (dead ++ [(Loc.base ⟨na⟩, mhG bMap), (Loc.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) ch)
  exact h21

/-- **The placement- and name-generic counting LOOP** (strong induction
on the remaining count): from the exit-test delivery at value `i`, the
run folds every remaining value into the counts map — `84·(L−i)` steps
EXACTLY, two fresh dead cells per iteration — and ends at the exit
test's `false` delivery over the full fold. The EXIT itself is
deliberately excluded (consumers differ there; see the module
docstring): each example chains its own exit tower from
`.retV (.bool false) cmp`. Lifted from `wcLoop_generic` (GAP-C1) with
the exit stripped; the body statements never appear in the loop's own
hypotheses, so it needs no `slVar` at all. -/
theorem mapCountLoop_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp : Cont) (env2g : LocalEnv)
    (hlen : ws.length < 2 ^ 63)
    (hIter : ∀ (i : Nat) (dead : Heap) (na : Nat) (ch : Choices),
      i < ws.length → base0 ≤ na → DeadFrom dead na →
      stepFnIter 53 (S (countsFold (ws.take i)) ((i : Nat) : Int) false dead
          na) (.retV (.bool true) cmp) ch
        = .ok (head,
            S (countsFold (ws.take (i + 1))) ((i : Nat) : Int) false
              (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch))
    (hA1 : ∀ kvs iv dead na ch,
      stepFnIter 29 (S kvs iv false dead na) head ch
        = .ok (.retV (wsHG bArr ws.length)
              (.strictK (.lengthOf (some (.slice tU64))) [] [] env2g
                (.strictK .lessCmp
                  [.int (IntKind.normalize .int
                    (IntKind.normalize .int (iv + 1))) .int]
                  [] env2g cmp)),
            S kvs (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
              false dead na, ch)) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), base0 ≤ na → DeadFrom dead na →
    ∀ ch : Choices,
    ∃ (tail : Heap),
      DeadFrom tail (na + 2 * n)
      ∧ stepFnIter (84 * n)
          (S (countsFold (ws.take i)) ((i : Nat) : Int) false dead na)
          (.retV (.bool (decide (((i : Nat) : Int) < (ws.length : Int)))) cmp)
          ch
        = .ok (.retV (.bool false) cmp,
            S (countsFold ws) ((ws.length : Nat) : Int) false tail
              (na + 2 * n), ch) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi dead na hna hdead ch
    rcases Nat.lt_or_ge i ws.length with hlt | hge
    · -- iterate
      rw [show (decide (((i : Nat) : Int) < (ws.length : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hIt := hIter i dead na ch hlt hna hdead
      have hdead₂ : DeadFrom (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) :=
        DeadFrom.push2 hdead
      have hA1' := hA1 (countsFold (ws.take (i + 1))) ((i : Nat) : Int)
        (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63),
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63)] at hA1'
      have hLen := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply (done := []) (env := env2g)
          (k := .strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] env2g
            cmp)
          (ch := ch)
          (GoLean.SliceMem.applyStrictOp_len_slice
            (σ := S (countsFold (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (b := .base ⟨bArr⟩) (off := 0) (len := ws.length)
            (cap := ws.length) (elem := tU64) (Nat.le_refl _)))
      have hCmp := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply
          (done := [.int ((i + 1 : Nat) : Int) .int]) (env := env2g)
          (k := cmp) (ch := ch)
          (GoLean.SliceMem.applyStrictOp_lessCmp_int
            (σ := S (countsFold (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (a := ((i + 1 : Nat) : Int)) (b := ((ws.length : Nat) : Int))
            (k := .int) (k' := .int)))
      obtain ⟨tail, htail, hrun⟩ := ih (n - 1) (by omega)
        (i + 1) (by omega) (by omega)
        (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)
        (by omega) hdead₂ ch
      refine ⟨tail, ?_, ?_⟩
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact htail
      · have hchain := stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hIt hA1')
            hLen) hCmp) hrun
        rw [show 53 + 29 + 1 + 1 + 84 * (n - 1) = 84 * n from by omega]
          at hchain
        rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact hchain
    · -- exit: i = ws.length, n = 0 — zero steps, the false delivery
      have hiL : i = ws.length := by omega
      subst hiL
      have hn0 : n = 0 := by omega
      subst hn0
      rw [show (decide (((ws.length : Nat) : Int) < ((ws.length : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      refine ⟨dead, ?_, ?_⟩
      · simpa using hdead
      · rw [List.take_length]
        rfl

/-! ## API group 3 — placing the loop: the per-placement discharge
pack (GAP-C1, second half)

The nine CONDITIONED discharges every counting-loop placement had to
re-derive (`init1`/`st1`/`init2`/`st2`/`var1`/`var2`/`read`/`mapGet`/
`mapAsgn` — ~270 lines per placement, four landed copies) are proven
ONCE here over an abstract placement: a base state `base`, a live
front `front kvs iv`, and nine placement FACTS, each of which a
consumer discharges by `rfl` or by its existing front-freshness lemma.
`mapCountIter_at` bundles them: placement facts + the 11 `rfl`
segments give the 53-step iteration directly. -/

private theorem defaultValue_tMap (σ : ExecState) :
    defaultValue σ tMap = .ok (.map ⟨none⟩) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

private theorem defaultValue_tU64 (σ : ExecState) :
    defaultValue σ tU64 = .ok (.int 0 .uint64) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

private theorem normMapHandle (σ : ExecState) (a : Addr) :
    normalizeValueForTy σ tMap (.map ⟨some (.base a)⟩)
      = .ok (.map ⟨some (.base a)⟩) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

private theorem normU64 (σ : ExecState) {w : Int}
    (hw : IntKind.normalize .uint64 w = w) :
    normalizeValueForTy σ tU64 (.int w .uint64) = .ok (.int w .uint64) := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel]
  rw [hw]
  rfl

/-- **The bundled per-placement counting iteration** (53 steps): the
nine placement facts + the eleven raw segments give
`mapCountIter_generic`'s conclusion directly — the conditioned
discharges are constructed inside, so a placement never re-derives
them. The placement facts:

* `hS` — the state family is the base-state record update over the
  live front (a `rfl` at every landed placement);
* `hnone` — the front owns no address ≥ `base0` (the placement's
  existing front-freshness lemma);
* `hmapCell`/`harrCell` — the map data cell at `bMap`, the input
  backing at `bArr` (`rfl`);
* `hsetMap` — writing the map data cell advances the front's `kvs`
  index (`rfl`);
* `hDecl1`/`hDecl2` — the `$c1`/`$c2` declarations produce the
  placement's loop-body environments (`rfl`);
* `hEnv1`/`hEnv2` — those environments resolve `$c1`/`$c2` at
  `na₀`/`na₀ + 1` (`rfl`). -/
theorem mapCountIter_at (slVar mapVar c1 c2 iVar : String)
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (base : ExecState) (front : List (Int × Nat) → Int → Heap)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp postK : Cont)
    (env3g : LocalEnv) (u1Envg uEnvg : Nat → LocalEnv)
    -- the placement facts
    (hS : ∀ kvs iv dead na, S kvs iv false dead na
      = { base with heap := front kvs iv ++ dead, nextAddr := na })
    (hnone : ∀ kvs iv x, base0 ≤ x →
      Heap.lookup (front kvs iv) (.base ⟨x⟩) = none)
    (hmapCell : ∀ kvs iv, Heap.lookup (front kvs iv) (.base ⟨bMap⟩)
      = some ⟨none, .mapData (toEntries kvs)⟩)
    (harrCell : ∀ kvs iv, Heap.lookup (front kvs iv) (.base ⟨bArr⟩)
      = some ⟨some (.array ws.length tU64),
          .array ⟨ws.map (fun v => .int v .uint64)⟩⟩)
    (hsetMap : ∀ kvs iv (w : Int) (v : Nat),
      Heap.set (front kvs iv) (.base ⟨bMap⟩)
          ⟨none, .mapData (toEntries (setk kvs w v))⟩
        = front (setk kvs w v) iv)
    (hDecl1 : ∀ na : Nat, env3g.declare c1 (.base ⟨na⟩) = u1Envg na)
    (hDecl2 : ∀ na₀ : Nat,
      (u1Envg na₀).declare c2 (.base ⟨na₀ + 1⟩) = uEnvg na₀)
    (hEnv1 : ∀ na₀ : Nat,
      LocalEnv.lookup (uEnvg na₀) c1 = some (.base ⟨na₀⟩))
    (hEnv2 : ∀ na₀ : Nat,
      LocalEnv.lookup (uEnvg na₀) c2 = some (.base ⟨na₀ + 1⟩))
    -- the raw segments (as in `mapCountIter_generic`)
    (hC1 : ∀ kvs iv dead na ch,
      stepFnIter 7 (S kvs iv false dead na) (.retV (.bool true) cmp) ch
        = .ok (.exec (.initialization { id := c1, typ := tMap }) env3g
            (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] env3g postK),
          S kvs iv false dead na, ch))
    (hC2 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀)
            postK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
              [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC3 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK))) ch
        = .ok (.exec (.initialization { id := c2, typ := tU64 })
              (u1Envg na₀)
              (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK),
          S kvs iv false dead na, ch))
    (hC4 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 8 (S kvs iv false dead na)
          (.next (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (uEnvg na₀) postK)) ch
        = .ok (.retV (.int iv .int)
              (.strictK .indexGet [wsHG bArr ws.length] [] (uEnvg na₀)
                (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                  (.seqn #[]) (uEnvg na₀)
                  (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))),
          S kvs iv false dead na, ch))
    (hC5 : ∀ kvs iv dead na₀ na (w : GoValue) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
            (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
              (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC6 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 4 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c1) (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 []
                [.var c2,
                 .add (.mapGet (.var c1) (.var c2) tU64 tU64)
                   (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC7 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.stmtOpK (.mapAssign tU64 tU64) 0 []
              [.var c2,
               .add (.mapGet (.var c1) (.var c2) tU64 tU64)
                 (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c2) (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
                [.add (.mapGet (.var c1) (.var c2) tU64 tU64)
                  (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC8 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int w .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
              [.add (.mapGet (.var c1) (.var c2) tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var c1) (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [] [.var c2] (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hC9 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.strictK (.mapGet tU64 tU64) [] [.var c2] (uEnvg na₀)
              (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                (.stmtOpK (.mapAssign tU64 tU64) 0
                  [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                  (uEnvg na₀) (.seq [] (uEnvg na₀) postK))))) ch
        = .ok (.evalE (.var c2) (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hC10 : ∀ kvs iv dead na₀ na (w cv : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int cv .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))) ch
        = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC11 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.next (.seq [] (uEnvg na₀) postK)) ch
        = .ok (head, S kvs iv false dead na, ch))
    -- the iteration-level hypotheses
    (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat)
    (ch : Choices)
    (hi : i < ws.length)
    (hw0 : 0 ≤ ws.getD i 0) (hw64 : ws.getD i 0 < 2 ^ 64)
    (hcnt : cnt kvs (ws.getD i 0) + 1 < 2 ^ 64)
    (hna : base0 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53 (S kvs ((i : Nat) : Int) false dead na)
        (.retV (.bool true) cmp) ch
      = .ok (head,
          S (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1))
            ((i : Nat) : Int) false
            (dead ++ [(Loc.base ⟨na⟩, mhG bMap),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  -- the nine conditioned discharges, constructed from the placement
  -- facts
  have hInit1 : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := c1, typ := tMap }) env3g
            (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] env3g postK)) ch
        = .ok (.next (.seq [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na)
              postK),
          S kvs iv false (dead ++ [(Loc.base ⟨na⟩, nilMapCell)]) (na + 1),
          ch) := by
    intro kvs iv dead na ch hna hdead
    rw [hS kvs iv dead na, hS kvs iv (dead ++ [(Loc.base ⟨na⟩, nilMapCell)])
      (na + 1), ← hDecl1 na]
    have hmiss : Heap.lookup (front kvs iv ++ dead) (.base ⟨na⟩) = none := by
      rw [lookup_append_right (hnone kvs iv na hna)]
      exact hdead na (Nat.le_refl na)
    have h := stepFn_init_seq
      (σ := { base with heap := front kvs iv ++ dead, nextAddr := na })
      (p := { id := c1, typ := tMap })
      (rest := [asgnC1G mapVar c1, seqnC2G slVar c2 iVar, mapAsgnG c1 c2]) (env := env3g)
      (k := postK) (ch := ch) (v := .map ⟨none⟩) (defaultValue_tMap _)
    rw [show ({ base with heap := front kvs iv ++ dead, nextAddr := na }
          : ExecState).nextAddr = na from rfl,
      show ({ base with heap := front kvs iv ++ dead, nextAddr := na }
          : ExecState).heap = front kvs iv ++ dead from rfl,
      set_fresh hmiss, List.append_assoc] at h
    exact h
  have hSt1 : ∀ kvs iv dead na₀ na ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2G slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)),
          S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) na, ch) := by
    intro kvs iv dead na₀ na ch hna hdead
    rw [hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]) na,
      hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) na]
    have hlook : Heap.lookup ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]),
          nextAddr := na } : ExecState).heap (.base ⟨na₀⟩)
        = some ⟨some tMap, .map ⟨none⟩⟩ := by
      show Heap.lookup
        (front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]))
        (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
      rw [lookup_append_right (hnone kvs iv na₀ hna),
        lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
      exact lookup_singleton_self
    have h := storeTarget_addr (v := .map ⟨some (.base ⟨bMap⟩)⟩)
      (v' := .map ⟨some (.base ⟨bMap⟩)⟩) hlook (normMapHandle _ _)
    rw [show ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]),
          nextAddr := na } : ExecState).heap
        = front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, nilMapCell)]) from rfl,
      set_append_right (hnone kvs iv na₀ hna),
      set_append_right (hdead na₀ (Nat.le_refl na₀)),
      set_singleton_self] at h
    exact stepFn_store_step h
  have hInit2 : ∀ kvs iv dead na₀ ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) (na₀ + 1))
          (.exec (.initialization { id := c2, typ := tU64 }) (u1Envg na₀)
            (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (u1Envg na₀) postK)) ch
        = .ok (.next (.seq [asgnReadG slVar c2 iVar, mapAsgnG c1 c2] (uEnvg na₀) postK),
          S kvs iv false
            (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
    intro kvs iv dead na₀ ch hna hdead
    rw [hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) (na₀ + 1),
      hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
        (.base ⟨na₀ + 1⟩, u64cell 0)]) (na₀ + 2), ← hDecl2 na₀]
    have hmiss : Heap.lookup
        (front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]))
        (.base ⟨na₀ + 1⟩) = none := by
      rw [lookup_append_right (hnone kvs iv (na₀ + 1) (by omega)),
        lookup_append_right (hdead (na₀ + 1) (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl
    have h := stepFn_init_seq
      (σ := { base with
        heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]),
        nextAddr := na₀ + 1 })
      (p := { id := c2, typ := tU64 })
      (rest := [asgnReadG slVar c2 iVar, mapAsgnG c1 c2])
      (env := u1Envg na₀) (k := postK) (ch := ch) (v := .int 0 .uint64)
      (defaultValue_tU64 _)
    rw [show ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]),
          nextAddr := na₀ + 1 } : ExecState).nextAddr = na₀ + 1 from rfl,
      show ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]),
          nextAddr := na₀ + 1 } : ExecState).heap
        = front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap)]) from rfl,
      set_fresh hmiss, List.append_assoc, List.append_assoc] at h
    exact h
  have hSt2 : ∀ kvs iv dead na₀ na (w : Int) ch, 0 ≤ w → w < 2 ^ 64 →
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell 0)])
          na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnG c1 c2] (uEnvg na₀) postK)),
          S kvs iv false
            (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
    intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
    rw [hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
        (.base ⟨na₀ + 1⟩, u64cell 0)]) na,
      hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
        (.base ⟨na₀ + 1⟩, u64cell w)]) na]
    have hlook : Heap.lookup ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
            (.base ⟨na₀ + 1⟩, u64cell 0)]),
          nextAddr := na } : ExecState).heap (.base ⟨na₀ + 1⟩)
        = some ⟨some tU64, .int 0 .uint64⟩ := by
      show Heap.lookup
        (front kvs iv ++ (dead ++ ([(Loc.base ⟨na₀⟩, mhG bMap)]
          ++ [(Loc.base ⟨na₀ + 1⟩, u64cell 0)])))
        (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
      rw [lookup_append_right (hnone kvs iv (na₀ + 1) (by omega)),
        lookup_append_right (hdead (na₀ + 1) (by omega)),
        lookup_append_right (show Heap.lookup [(Loc.base ⟨na₀⟩, mhG bMap)]
            (.base ⟨na₀ + 1⟩) = none from by
          rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
          rfl)]
      exact lookup_singleton_self
    have h := storeTarget_addr (v := .int w .uint64) (v' := .int w .uint64)
      hlook (normU64 _ (unorm_of_range hw0 hw64))
    rw [show ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
            (.base ⟨na₀ + 1⟩, u64cell 0)]),
          nextAddr := na } : ExecState).heap
        = front kvs iv ++ (dead ++ ([(Loc.base ⟨na₀⟩, mhG bMap)]
          ++ [(Loc.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
      set_append_right (hnone kvs iv (na₀ + 1) (by omega)),
      set_append_right (hdead (na₀ + 1) (by omega)),
      set_append_right (show Heap.lookup [(Loc.base ⟨na₀⟩, mhG bMap)]
          (.base ⟨na₀ + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
        rfl),
      set_singleton_self] at h
    exact stepFn_store_step h
  have hlk : ∀ kvs iv (w : Int) dead na₀ na, base0 ≤ na₀ →
      DeadFrom dead na₀ →
      (Heap.lookup ({ base with
          heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
            (.base ⟨na₀ + 1⟩, u64cell w)]),
          nextAddr := na } : ExecState).heap (.base ⟨na₀⟩)
          = some (mhG bMap)
        ∧ Heap.lookup ({ base with
            heap := front kvs iv ++ (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
              (.base ⟨na₀ + 1⟩, u64cell w)]),
            nextAddr := na } : ExecState).heap (.base ⟨na₀ + 1⟩)
          = some (u64cell w)) := by
    intro kvs iv w dead na₀ na hna hdead
    constructor
    · show Heap.lookup
        (front kvs iv ++ (dead ++ ([(Loc.base ⟨na₀⟩, mhG bMap)]
          ++ [(Loc.base ⟨na₀ + 1⟩, u64cell w)])))
        (.base ⟨na₀⟩) = some (mhG bMap)
      rw [lookup_append_right (hnone kvs iv na₀ hna),
        lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
      exact lookup_append_left lookup_singleton_self
    · show Heap.lookup
        (front kvs iv ++ (dead ++ ([(Loc.base ⟨na₀⟩, mhG bMap)]
          ++ [(Loc.base ⟨na₀ + 1⟩, u64cell w)])))
        (.base ⟨na₀ + 1⟩) = some (u64cell w)
      rw [lookup_append_right (hnone kvs iv (na₀ + 1) (by omega)),
        lookup_append_right (hdead (na₀ + 1) (by omega)),
        lookup_append_right (show Heap.lookup [(Loc.base ⟨na₀⟩, mhG bMap)]
            (.base ⟨na₀ + 1⟩) = none from by
          rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
          rfl)]
      exact lookup_singleton_self
  have hVar1 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var c1) (uEnvg na₀) k) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩) k,
            S kvs iv false
              (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
                (.base ⟨na₀ + 1⟩, u64cell w)]) na, ch) := by
    intro kvs iv w dead na₀ na k ch hna hdead
    rw [hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
      (.base ⟨na₀ + 1⟩, u64cell w)]) na]
    exact stepFn_var (hEnv1 na₀) (hlk kvs iv w dead na₀ na hna hdead).1
  have hVar2 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap), (Loc.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var c2) (uEnvg na₀) k) ch
        = .ok (.retV (.int w .uint64) k,
            S kvs iv false
              (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
                (.base ⟨na₀ + 1⟩, u64cell w)]) na, ch) := by
    intro kvs iv w dead na₀ na k ch hna hdead
    rw [hS kvs iv (dead ++ [(Loc.base ⟨na₀⟩, mhG bMap),
      (.base ⟨na₀ + 1⟩, u64cell w)]) na]
    exact stepFn_var (hEnv2 na₀) (hlk kvs iv w dead na₀ na hna hdead).2
  have hRead : ∀ kvs (i : Nat) dead na, i < ws.length →
      applyStrictOp (S kvs ((i : Nat) : Int) false dead na) .indexGet
          [wsHG bArr ws.length, .int ((i : Nat) : Int) .int]
        = .ok (.int (ws.getD i 0) .uint64,
            S kvs ((i : Nat) : Int) false dead na) := by
    intro kvs i dead na hi
    rw [hS kvs ((i : Nat) : Int) dead na]
    have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
        = some (.int (ws.getD i 0) .uint64) := by
      rw [Nat.zero_add, getElem?_mapU ws i hi]
    have hlook : Heap.lookup ({ base with
          heap := front kvs ((i : Nat) : Int) ++ dead, nextAddr := na }
          : ExecState).heap (.base ⟨bArr⟩)
        = some ⟨some (.array ws.length tU64),
            .array ⟨ws.map (fun v => .int v .uint64)⟩⟩ := by
      show Heap.lookup (front kvs ((i : Nat) : Int) ++ dead) (.base ⟨bArr⟩)
        = _
      exact lookup_append_left (harrCell kvs ((i : Nat) : Int))
    exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
      (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) hlook
      (Nat.le_refl ws.length) hi hget
  have hMapGet : ∀ kvs iv dead na (w : Int), 0 ≤ w → w < 2 ^ 64 →
      applyStrictOp (S kvs iv false dead na) (.mapGet tU64 tU64)
          [.map ⟨some (.base ⟨bMap⟩)⟩, .int w .uint64]
        = .ok (.int (cnt kvs w : Int) .uint64, S kvs iv false dead na) := by
    intro kvs iv dead na w hw0 hw64
    rw [hS kvs iv dead na]
    have hlook : Heap.lookup ({ base with
          heap := front kvs iv ++ dead, nextAddr := na }
          : ExecState).heap (.base ⟨bMap⟩)
        = some ⟨none, .mapData (toEntries kvs)⟩ := by
      show Heap.lookup (front kvs iv ++ dead) (.base ⟨bMap⟩) = _
      exact lookup_append_left (hmapCell kvs iv)
    exact applyStrictOp_mapGet (a := ⟨bMap⟩) (dty := none) hlook
      (unorm_of_range hw0 hw64)
  have hMapAsgn : ∀ kvs iv dead na₀ na (w : Int) (v : Nat) ch,
      0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
      stepFn (S kvs iv false dead na)
          (.retV (.int ((v : Nat) : Int) .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0
              [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.next (.seq [] (uEnvg na₀) postK),
            S (setk kvs w v) iv false dead na, ch) := by
    intro kvs iv dead na₀ na w v ch hw0 hw64 hv
    rw [hS kvs iv dead na, hS (setk kvs w v) iv dead na]
    have hlook : Heap.lookup ({ base with
          heap := front kvs iv ++ dead, nextAddr := na }
          : ExecState).heap (.base ⟨bMap⟩)
        = some ⟨none, .mapData (toEntries kvs)⟩ := by
      show Heap.lookup (front kvs iv ++ dead) (.base ⟨bMap⟩) = _
      exact lookup_append_left (hmapCell kvs iv)
    have hMA := mapAssignValue_toEntries (a := ⟨bMap⟩) (v := v) hlook
      (unorm_of_range hw0 hw64)
      (unorm_of_range (by omega) (by exact_mod_cast hv))
    rw [show Heap.set ({ base with
          heap := front kvs iv ++ dead, nextAddr := na }
          : ExecState).heap (.base ⟨bMap⟩)
          ⟨none, .mapData (toEntries (setk kvs w v))⟩
        = front (setk kvs w v) iv ++ dead from by
      rw [show ({ base with heap := front kvs iv ++ dead, nextAddr := na }
            : ExecState).heap = front kvs iv ++ dead from rfl,
        set_append_left (hmapCell kvs iv), hsetMap kvs iv w v]] at hMA
    exact stepFn_mapAssign_apply hMA
  exact mapCountIter_generic slVar mapVar c1 c2 iVar S ws bArr bMap base0 head cmp postK
    env3g u1Envg uEnvg hC1 hInit1 hC2 hSt1 hC3 hInit2 hC4 hRead hC5 hSt2
    hC6 hVar1 hVar2 hC7 hC8 hC9 hMapGet hC10 hMapAsgn hC11
    kvs i dead na ch hi hw0 hw64 hcnt hna hdead

/-! ## API group 4 — ranging over a map: the pick loop (GAP-R1)

The §10b choice-pick induction, stated ONCE over an abstract state
descriptor: the whole per-iteration content — body, binders,
allocation, accumulator effect — enters through the single `hIter`
hypothesis ("given the pick, one iteration takes the state at `d` to
the state at some `d'` preserving the invariant, within `c` steps"),
so neither the body nor the binder shape appears in the schema. The
consumer encodes its accumulator law as a CONSERVATION invariant `P`
(wordcount: the max-fold of `best` and the remaining values is
constant; histogram: `distinct` plus the remaining count is constant),
which is exactly how order-invariance under every pick becomes a
provable loop fact. -/

/-- `Choices.consume`'s `% bound` contract: the pick is in range
(promoted from the two per-example copies — GAP-R1). -/
theorem consume_lt (ch : Choices) {n : Nat} (hn : 0 < n) :
    (Choices.consume ch n).1 < n := by
  cases ch with
  | nil => simpa [Choices.consume] using hn
  | cons c rest =>
      simp only [Choices.consume]
      have : max 1 n = n := by omega
      rw [this]
      exact Nat.mod_lt _ hn

/-- Erasing the picked entry shortens the snapshot by exactly one
(promoted — GAP-R1). -/
theorem eraseIdx_length_of_lt {α : Type} {l : List α} {idx : Nat}
    (h : idx < l.length) : (l.eraseIdx idx).length = l.length - 1 := by
  rw [List.length_eraseIdx]
  simp [h]

/-- Membership survives an erase (promoted — GAP-R1). -/
theorem mem_of_mem_eraseIdx {α : Type} :
    ∀ {l : List α} {i : Nat} {a : α}, a ∈ l.eraseIdx i → a ∈ l := by
  intro l
  induction l with
  | nil => intro i a h; cases h
  | cons x rest ih =>
      intro i a h
      cases i with
      | zero =>
          rw [List.eraseIdx_cons_zero] at h
          exact List.mem_cons.mpr (.inr h)
      | succ n =>
          rw [List.eraseIdx_cons_succ] at h
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (.inl h)
          · exact List.mem_cons.mpr (.inr (ih h))

/-- **The choice-pick loop, at every choice stream** (GAP-R1): from a
snapshot `rem` with the invariant `P d rem`, the loop drains the
snapshot — one consumed choice and one erased entry per iteration
(`hIter`), `e` steps to exit at the empty snapshot (`hExit`) — within
`c·|rem| + e` steps, ending at `exitCfg` in a state satisfying
`P d' []`. -/
theorem mapPickLoop_generic {δ : Type}
    (T : δ → ExecState) (cfg : List (Int × Nat) → Config)
    (exitCfg : Config) (P : δ → List (Int × Nat) → Prop)
    (c e : Nat)
    (hIter : ∀ (d : δ) (rem : List (Int × Nat)) (idx : Nat)
      (p : Int × Nat) (ch ch₂ : Choices),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p → P d rem →
      ∃ (k : Nat) (d' : δ), k ≤ c ∧ P d' (rem.eraseIdx idx) ∧
        stepFnIter k (T d) (cfg rem) ch
          = .ok (cfg (rem.eraseIdx idx), T d', ch₂))
    (hExit : ∀ (d : δ) (ch : Choices), P d [] →
      stepFnIter e (T d) (cfg []) ch = .ok (exitCfg, T d, ch)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (d : δ) (ch : Choices), P d rem →
    ∃ (k : Nat) (d' : δ) (ch' : Choices),
      k ≤ c * m + e ∧ P d' [] ∧
      stepFnIter k (T d) (cfg rem) ch = .ok (exitCfg, T d', ch') := by
  intro m
  induction m with
  | zero =>
      intro rem hm d ch hP
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      exact ⟨e, d, ch, by omega, hP, hExit d ch hP⟩
  | succ m ih =>
      intro rem hm d ch hP
      rcases hcons : Choices.consume ch rem.length with ⟨idx, ch₂⟩
      have hidx : idx < rem.length := by
        have := consume_lt ch (show 0 < rem.length by omega)
        rw [hcons] at this
        exact this
      obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
        ⟨_, List.getElem?_eq_getElem hidx⟩
      obtain ⟨k₁, d₁, hk₁, hP₁, hrun₁⟩ :=
        hIter d rem idx p ch ch₂ hcons hidx hp hP
      obtain ⟨k₂, d₂, ch', hk₂, hP₂, hrun₂⟩ :=
        ih (rem.eraseIdx idx)
          (by rw [eraseIdx_length_of_lt hidx]; omega) d₁ ch₂ hP₁
      refine ⟨k₁ + k₂, d₂, ch', ?_, hP₂,
        stepFnIter_chain hrun₁ hrun₂⟩
      have hms : c * (m + 1) = c * m + c := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

end GoLean.MapLoops
