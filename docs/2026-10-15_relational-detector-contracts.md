# D1 detector contracts

Baseline: audited C1 `55ad72493061b59363e846341380a9edce12a2de`.
Branch: `spike/relational-detector-contracts-1015`, isolated worktree
`.claude/worktrees/relational-detector-contracts-1015`. Its `.lake`, experiment `.lake`, Go
build cache and temporary files are private to this lane.

## Decisions and provenance

- [USER] 2026-10-15: execute the relayed D1 charter independently of C2,
  permitting limited behavior-preserving operational changes; no merge,
  push, live repin or peer writes.
- [AGENT] 2026-10-15: carry the experiment sources and historical stage/review
  verbatim from `f6f37e36f4844d7e3730496a4fa23b48e5a48e0e` via `git restore
  --source`, preserving its original branch/worktree. Historical reports
  describe that pin; this document records D1 and supersedes their open
  obligations only when proved here.

- [AGENT] 2026-10-15: replace only the recursive location comparator's
  implementation, retaining its instance/declaration names and exact
  constructor/component order. Keep shadow insertion, overlap,
  canonicalization, clock operations, scheduling and driver behavior as
  written. Export proof contracts through `GoLean.Relational`.

## Contracts and scope

`GoLean/GoCore/LocationOrder.lean` supplies a structurally recursive
`instOrdLoc.ord`, equality coherence (`loc_compare_eq_iff`), orientation
(`loc_compare_swap`) and strict transitivity (`loc_compare_lt_trans`).
`Std.LawfulEqOrd Loc` and `Std.TransOrd Loc` package these facts; they cover
arbitrary finite locations, including arbitrary static field type names,
field names and signed indices. No root-only or canonical-key restriction.

`ShadowOrder.lean` proves that the existing derived key comparator equals
comparison of `ShadowKey.orderCode`, an injective lexicographic encoding.
This checks its actual order: data < syncWord < chanObj; location first,
then sync kind and word in declaration order. The checked `LawfulEqOrd`,
`TransOrd` and `LawfulBEq` instances relate ordering, structural equality
and the detector's Boolean key lookup. The encoding is proof infrastructure;
the executable still uses its existing key comparator.

`ShadowHistory.lean` concerns the **existing** `shadowSet` and detector:

- `shadowSet_lookup_self` returns the new value at the updated key.
  `shadowSet_lookup_other` and `shadowSet_other_mem` preserve every other
  exact key, with no sortedness or non-overlap premise.
- `ShadowOrdered` is strict pairwise key order. `.keys_nodup` proves key
  uniqueness. `shadowSet_ordered` preserves that invariant. Together with
  lookup, this rules out duplicate residual entries at a replaced key.
- `RaceState.accessKey_ordered`, `.event_ordered`, `.events_ordered` and
  `raceUpdate_ordered` propagate the invariant through successful real
  detector folds. `PoolPrefix.shadow_ordered_empty` derives it from the
  empty initial detector along actual checked prefixes; it is not assumed
  at the final use site.
- `RaceState.accessKey_other` and `PoolPrefix.preserves_lookup` preserve a
  history across successful updates/prefixes whose events avoid the exact
  key, including nested attribution and HB actions. HB changes clocks, not
  shadow cells. The success premise retains conflict checking. Overlapping
  accesses may have different keys and both histories survive.
- `RaceState.accessKey_reject_of_mem` turns a retained overlapping,
  conflicting history into the actual detector's rejection.

Structural key equality is not canonicalization or overlap. `Loc.canon`
erases static field type spelling at event emission; it is unchanged.
Parent/child paths can be different structural keys while overlapping.
Neither key inequality nor retained shadow history asserts heap ownership
or the absence of races. No all-schedule safety, general locality,
sequentialization or Iris lifting/adequacy result is claimed.

The original 25-iteration disjoint-memory and 38-iteration rendezvous
executions retain their driver statements, labels/output, attribution,
scheduling picks, detector success and sender-to-receiver HB. Their inputs
remain supplied `execProg` states, not proved whole-program/frontend setup.
The comparator case splits in their proofs are replaced by checked reduction.

`Concurrency.root_comparator_contract` closes the old root regression.
`Concurrency.Sync.gap_checked` follows the **actual** 16 steps from the
post-write state (13 iterations) to receiver parking (29 iterations).
`pre_pair_ordered` derives its invariant from the empty initial detector.
`pre_pair_history` uses the general prefix law to retain the write to x
through unrelated channel-handle accesses. `pre_pair_rejection` uses that
retained cell, its checked conflicting clock, and the general rejection law
to close `PrePairRejection` unconditionally. It is a negative detector probe
at a reached state, not a newly schedulable parent read.

The historical `equal_comparison_loses_rejection` remains a conditional
statement whose premise is now disproved by `comparison_not_equal`. It was
never evidence of a runtime miscomparison. `Concurrency.Obstruction` now
checks a transparent safe definition and proves the root regression instead
of expecting opacity; the audit continues reporting other findings.

## Operational delta and preservation argument

Only `Loc` comparison changes implementation. The `Addr` and `TypeId`
derived instances move unchanged from `Ops.lean` to `LocationOrder.lean`.
The latter is imported by `Ops`; no key constructor, field, list insertion,
clock update or scheduling function is edited.

The old generated body was inspected at C1 with
`#print GoLean.GoCore.instOrdLoc.ord._unsafe_rec`. Lean 4.32.2's
`Lean/Elab/Deriving/Ord.lean`, `mkMatchOld`/`mkAuxFunction`, generates:
constructor order base < field < index; within a base compare `Addr`; within
a field recursively compare the base, then `TypeId`, then field name; within
an index recursively compare the base, then signed index. Components combine
with short-circuiting `Ordering.then`, ending in `.eq`. The `Addr`/`TypeId`
wrappers compare their sole Nat/String fields. The only recursive calls
are on strict sublocations, so this source algorithm terminates on every
finite `Loc` even though the deriving handler classified it as partial.

`locComparisonStep` states that exact generated body with the recursive
function as a parameter. `loc_compare_unfold` proves the replacement
satisfies it, including the old wrapper definitions and trailing `.eq`.
`loc_comparison_unique` proves **any** function satisfying those equations
agrees with the replacement on every location. The old opaque constant
does not expose those equations, so this is **not** a kernel theorem of
equality to that constant. The connection to its executed implementation
rests on the separately reviewable generated-source argument and pinned
compiler, with executable controls as supporting evidence.

Preserving comparison results preserves the entire shadow list, not merely
lookup or accepted program outputs: `shadowSet`'s branch sequence is
unchanged. Consequently structural equality/order seen by exploration,
retained histories, later rejection decisions and their possible downstream
scheduling effects are covered by the same source argument. We do not call
internal history unobservable, nor infer universal equivalence from tests.

`DetectorControls.lean` is run unchanged against pre-repair C1 and the
candidate. It checks all pairs of 27 mixed/nested locations and 243 data,
canonical-data, channel and sync-word keys (59,778 comparisons), three
complete insertion/replacement sequences (forward, reverse, repeated) and
729 subsequent detector access probes. It includes differing static tags,
Unicode/empty field names, signed indices and overlapping distinct keys.
Their complete stdout matched byte-for-byte. No behavioral difference was
observed. This finite test is not a universal equivalence proof.

## Individual disposition of the 17 findings

Each name below ends in `._unsafe_rec`; the prefix is written in full.
The generated declarations are `DefinitionSafety.partial`, not classified
as `unsafe`. Only the comparator is repaired here. The other 16 remain
**findings**, not exceptions or waivers; the implementation scan remains
**FAIL**. The standard-axiom check is a separate result.

| Declaration prefix | Use and disposition |
| --- | --- |
| `GoLean.GoCore.instOrdLoc.ord` | **Fixed:** load-bearing shadow-key ordering. Transparent total definition plus the general laws above. |
| `GoLean.GoCore.instBEqExpr.beq` | **Open:** generated structural expression equality and composite instances. Not used by the detector fold. The checked comparison tower uses `Expr.eqbF`/soundness (`SyntaxEqb.lean`); this is not a lawfulness theorem for the derived instance. Future consumers using `==` on expressions need such a contract or the checked tower. |
| `GoLean.GoCore.instBEqStmt.beq` | **Open:** corresponding statement equality/composite instances; the checked tower uses `Stmt.eqbF`/soundness. No derived-equality adequacy claim. |
| `GoLean.GoCore.instReprTy.repr` | **Open:** type rendering, including `valueEq` refusal diagnostics reached from `stepFn`. Not in `raceUpdate`; exact diagnostic correspondence remains an adequacy obligation. |
| `GoLean.instReprGoValue.repr` | **Open:** value rendering, including `preprintDispatch` and malformed-operation diagnostics in the executed semantics. Not dismissed as unobservable; general text correspondence remains unproved. |
| `GoLean.GoCore.instReprExpr.repr` | **Open:** expression rendering, including `unseqAtom` refusal text. Not in the detector; future exact refusal-text claims must account for it. |
| `GoLean.GoCore.instReprStmt.repr` | **Open:** statement rendering, including nested syntax representations. No total representation correspondence supplied. |
| `GoLean.GoCore.Machine.instReprSeedValue.repr` | **Open:** seeded-fixture value representation. The detector consumes emitted keys/clocks, not this representation. Future claims observing seed-value rendering need a total account. |
| `GoLean.GoCore.Declaration.instReprTy.repr_1` | **Open:** takes `Declaration.Ty`, in the mutual printer family generated by deriving Repr for Ty. Identity uses `Ty.eqb`, not this printer. No total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprTy.repr_2` | **Open:** takes `Declaration.Field`, in the Ty-derived family; displays member/type/tag data. Identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprTy.repr_3` | **Open:** takes `Declaration.Method`, in the Ty-derived family; signature identity uses `Method.eqb`. No total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_1` | **Open:** takes `Declaration.Ty`, in the separate mutual family generated by deriving Repr for Field. Identity uses `Ty.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_2` | **Open:** takes `Declaration.Field`, in the Field-derived family; identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_3` | **Open:** takes `Declaration.Method`, in the Field-derived family; identity uses `Method.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_1` | **Open:** takes `Declaration.Ty`, in the separate mutual family generated by deriving Repr for Method. Identity uses `Ty.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_2` | **Open:** takes `Declaration.Field`, in the Method-derived family; identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_3` | **Open:** takes `Declaration.Method`, in the Method-derived family; identity uses `Method.eqb`. No detector dependence or total rendering theorem. |

These uses are checkable in `Value.lean`, `Syntax.lean`, `Declaration.lean`,
`Seed.lean`, `SyntaxEqb.lean`, and the diagnostic call sites in `Machine.lean`
and `Ops.lean`. A declaration-value dependency walk from `raceUpdate` found
only the location comparator among these opaque endpoints before repair;
after repair that path ends in a total definition. The walk from
`stepFn`/`stepMulti` additionally finds the Ty/GoValue/Expr diagnostic
printers above. It stops at opaque endpoints, so it is not a claim that
their executed bodies have no further dependencies. No unrelated printer
cleanup or new inventory gate is introduced.

## Validation and reproduction

The initial carried experiment was rebuilt on C1 before the operational edit:
both positive runs, axioms and the original 17-finding report reproduced.
All build state is private; `scripts/setup-deps --from /home/mike/projects/golean
--only goose,go` cloned the pinned read-only references locally with independent
objects. No peer build state or writable cache was attached.

- Final experiment/facade build: **PASS**, 77 jobs, warning-free. Headline
  axiom checks and the exhaustive imported-project audit: **PASS**, 21,517
  declarations, only `propext`, `Classical.choice`, `Quot.sound`.
- Implementation scan: **FAIL**, 16 findings, individually open above.
  This is not a clean implementation inventory or a waiver.
- Exact kernel replay: **PASS**. The 105-import aggregate and its complete
  closure replayed into an empty environment; all eight separate entry
  modules replayed successfully. Their imports are covered by the aggregate.
  An additional `Main --fresh` replay also passed.
- Archived-C1 executable preservation controls: **PASS**, complete output
  matched byte-for-byte. The old-constant proof limitation remains as stated.
- Fresh independent source review: complete; two documentation findings
  fixed individually. Immutable commit identity verification is pending;
  [review and dispositions](2026-10-15_relational-detector-review.md).
- Full `scripts/ci --diff`: **PASS**, 1,206 seconds under the deliberate
  cold-build 64 GB cap and two Lean threads. All default targets warning-free,
  core audit, Go unit tests, 396 interpreter tests, boundary checks and complete
  unsequenced-scheduler reference sets passed. Fresh differential: 3,989 rows,
  3,749 PASS / 240 baseline FAIL, no regression or cause drift. Fresh negative:
  405/405 PASS. All speedbumps passed; neither baseline was repinned. CI
  correctly reported that its records certify the dirty worktree content;
  the implementation commit contains that tested code unchanged.

From the candidate worktree root (Go 1.26.5 and Lean 4.32.2 installed):

```sh
scripts/setup-deps --from /home/mike/projects/golean --only goose,go
LEAN_NUM_THREADS=2 GOTOOLCHAIN=local GOPROXY=off GOTELEMETRY=off GOENV=off \
  GOPATH="$PWD/.tmp/gopath" GOMODCACHE="$PWD/.tmp/gomodcache" \
  capped -m 64G -- scripts/ci --diff
experiments/2026-10-14-concurrency-compatibility/check-preservation
cd experiments/2026-10-14-concurrency-compatibility
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean Concurrency/Audit.lean
```

For exact replay, still in the experiment directory, generate an ephemeral
imports-only aggregate of GoLean/Test modules plus this experiment. Executable
entry modules are replayed separately because their top-level `main` declarations
cannot coexist in one environment. The first aggregate attempt failed on that
name collision before replay; the split below covers every module. The C1
baseline does not contain main's newer replay script.
The aggregate replays its whole closure from an empty environment; each
separate entry module replays its own declarations into its imports, already
covered by the aggregate. This avoids repeating the same dependency replay
for every executable. An additional fresh replay of `Main` was also run.

```sh
python3 -c 'from pathlib import Path; root=Path("../.."); entries=["Main","Tests.GoCoreEval","Tests.DeclarationUnicode","Tests.DeclarationWire","Tests.UnseqWire","Tests.MethodIdentity","Tests.StrictJsonParse","Tests.UnseqScheduler"]; mods=["GoLean"]+[".".join(p.relative_to(root).with_suffix("").parts) for d in ["GoLean", "Tests"] for p in sorted((root/d).rglob("*.lean"))]+["Concurrency.Audit"]; Path(".lake/D1Replay.lean").write_text("\n".join("import "+m for m in mods if m not in entries)+"\n"); Path(".lake/D1Replay.entries").write_text("\n".join(entries)+"\n")'
LEAN_NUM_THREADS=2 capped lake env lean --root=.lake \
  -o .lake/build/lib/lean/D1Replay.olean .lake/D1Replay.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose D1Replay
LEAN_NUM_THREADS=2 capped bash -c 'set -e; while IFS= read -r module; do lake env leanchecker --verbose "$module"; done < .lake/D1Replay.entries'
```

The preserved experiment branch is untouched. Reproduction never builds in
it or in a peer tree. `check-preservation` archives the immutable C1 source
into a new private temporary directory, builds its Race closure, runs the
same controls against old/new code, and removes that temporary directory.
No baseline was repinned and no corpus result is being waived as an expected
effect of the repair.
