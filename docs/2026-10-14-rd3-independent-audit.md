# Independent RD3 call/return audit — 2026-10-14

## Target and outcome

Immutable implementation target: **`95f1eb64ca3bfa3c39fd5aa0792d516e76a31089`**.
Final comparison verified the exact set and bytes of all 97 GoLean/Tests Lean
source files against that commit; all six frozen implementation hashes are
unchanged. The final documentation and memory-inventory addition were also
reviewed.

Reviewed in the independent `audit/rd3-independent-1014` worktree, starting
at `918c1d8b`, with the six frozen implementation files copied bytewise.
No source or downstream worktree was modified by this reviewer.

No correctness defect or unmet obligation was found in the reviewed RD3
fragment. This is a useful semantic composition interface: the caller uses
an independently proved callee body and the same `SavedCaller.invoke` rule
for void fall-through and nonempty explicit return. It is not evidence that
the downstream Iris callers have migrated or that general call semantics,
observations, effects or defers have been covered.

[AGENT] 2026-10-14: validate the supplied compatibility harness independently,
then test read/write aliasing separately; retain the existing correction's
root restriction on callee result slots, not on caller destinations.

## Review conclusions

1. **Six exact corrected propositions pass.** The unchanged `ReferenceLaw`,
   `AssignVariableLaw`, `CallEntryLaw`, `ReturnStartLaw`, `ReturnSequenceLaw`
   and corrected `DeliverLaw` all have proofs through the public facade.
   Both unchanged conditional examples are instantiated without missing-law
   parameters. Adapters convert list predicates and old boundary views;
   they add no semantic assumptions.
2. **Call plumbing is actually upstream-owned.** `SavedCaller.enter` handles
   the argument walk and declared activation; `CallBoundary.deliver` handles
   frame exit, traced result reads, target resolution, ordered stores and
   cleanup. `SavedCaller.invoke` composes these with a separate body contract.
   The semantic client does not construct frames, target plans or signals.
   `keep_set` applies the existing `set_body` theorem without unfolding it.
   `identity_call` uses the same invocation rule with its separately proved
   explicit-return body and nonempty result.
3. **The repaired delivery domain is justified.** `LocalEntry.resultSlots`
   follows successful allocation/binding/pinning, including duplicate
   signature names, and needs no distinctness or well-formedness premise.
   `Readback.traced` uses the root restriction exactly where `loadRoot` and
   `loadLoc` would otherwise disagree. `invoke` obtains this invariant from
   activation. The malformed interior-result counterexample is not admitted
   by the repaired rule; the executable semantics was not changed.
4. **Aliasing remains admitted.** The delivery theorem quantifies arbitrary
   destination locations and sequential `WriteValues`; it imposes neither
   distinctness nor disjointness from result slots. Reviewer proofs checked
   both normal exit modes with repeated root destinations where the first
   write aliases a later result, and repeated interior array destinations.
   Both finish with the value read before any destination write, followed by
   writes in destination order. Caller continuations remain arbitrary.
5. **Labels and scope are honest.** `PickFreeRun` retains a list of actual
   relational transitions and constrains each pick list to empty. It does
   not replace access traces or assert output silence. Its definition is
   the existing downstream `Segment` proposition, so the refusal-sensitive
   progress composition remains usable. Declared non-method dispatch,
   store-preserving operands and an unchanged no-defer call boundary are
   explicit premises/shape restrictions. A body that changes its frame by
   registering defers cannot silently discharge the stated exit contract.
6. **Remaining coupling is explicit.** Clients still handle activation,
   semantic memory equations, result arity, local bindings, transparent
   states/continuations, and source sequence composition. Identity's concrete
   activation is constructed explicitly. This batch removes call-frame and
   return plumbing rather than providing a fully abstract program logic.
   Iris ownership and its ordered destination-update protocol remain
   downstream; production imports contain no Batteries, Iris or demo module.

No evaluator definition, transition rule, memory operation, choice domain
or differential baseline changed. The moved empty-sequence proof is the
same proof with public visibility for reuse. Documentation accurately states
the remaining scope and migration work; its reproduction proof blocks are
byte-identical to the checked harness files.

## Independent validation and reproducibility

Lean 4.32.2; every Lean/Lake job used `LEAN_NUM_THREADS=2` and `capped`.
Caches and Batteries were bytewise copies, without hardlinks or symlinks to
peer build trees. Copied build products for the changed modules and tests
were removed in the reviewer's own tree to force fresh elaboration. The
remaining unchanged GoLean dependencies used copied build products followed
by complete kernel replay; this was not a cold full build.

Commands from the review checkout:

```sh
LEAN_NUM_THREADS=2 capped lake build GoLean Tests.RelationalContracts Tests.GoCoreAudit
LEAN_NUM_THREADS=2 capped scripts/check-core-audit
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean
```

The fresh targeted build passed (88 jobs). The core audit passed for 80
GoLean modules excluding the root, 348 required theorems and 22,306 local
declarations, with only standard axioms. The full GoLean prefix replay
exited zero: its set of 81 unique module names equalled exactly all on-disk
GoLean sources including the root. No missing or stale module was accepted.

The frozen twelve-file downstream closure matches all hashes in
`2026-10-14_relational-call-acceptance.md`; in particular the corrected
request/acceptance hashes are `2571e366…12d6b` and `036ab43e…a2d`.
Batteries HEAD is `023ce7d62a0531e22a5331e20b587817a80d49ff`.
From the independent `.tmp/rd3` package configured as that document states:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean -o .lake/build/lib/lean/Adversarial.olean Adversarial.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Compatibility SemanticClient Adversarial RelationalDemo Batteries
```

The twelve frozen sources and two supplied harness modules were freshly
elaborated (66 jobs); all six laws, both original examples and the three
semantic-client theorems printed standard axioms only. Kernel replay also
included the reviewer's two alias tests in `Adversarial`; it exited zero and
the exact set was 18 modules: twelve frozen sources, the two supplied
harness modules, one reviewer module and the three built Batteries modules
(`CodeAction.Deprecated`, `Data.List.Basic`, `Tactic.Alias`). This is not a
replay of all Batteries sources. The two reviewer theorems printed standard
axioms only after successful elaboration.

The implementer reports `LEAN_NUM_THREADS=2 capped scripts/ci --diff` passing
in 741 seconds: build 194 jobs, 396 eval tests, 3,989 differential rows
(3,749 PASS and 240 classified known FAIL), and 405 negative rows, with
unchanged baselines. This full run is not claimed as an independent rerun.
Its one red speedbump was the missing `WriteValues`/`storeLoc` inventory row.
The final added row correctly describes a Prop-only premise: actual delivery
uses `storeTarget`/`Mem.store` and retains the emitted access label. I copied
the exact committed inventory to my own lane and independently ran
`scripts/check-mem-callsites`: PASS, 85 rows. No semantic source changed
after the independently validated freeze. No merge or push is authorized
by this review.

## Reproduce the supplemental alias checks

Save this as `.tmp/rd3/Adversarial.lean` before the commands above. The
root case keeps an arbitrary context; the array case uses an empty type
table so its concrete writes reduce without extra type-table premises.
Both quantify arbitrary caller continuations and either normal exit mode.

```lean
import GoLean.Relational
open GoLean GoLean.GoCore GoLean.GoCore.Relational
namespace RD3Adversarial

-- First write aliases the second result. Both values must be read before writes.
theorem read_before_alias_writes (ctx : ProgramCtx) (k : Continuation) (mode : NormalExit) :
    let s : Store := {heap := #[.value .bool (.bool false), .value .bool (.bool true)]}
    let b : CallBoundary := ⟨⟨[7, 7], LocalEnv.declare [] 7 (.base ⟨0⟩), k⟩,
      ⟨"Alias"⟩, [.base ⟨1⟩, .base ⟨0⟩]⟩
    PickFreeRun ctx (b.exit mode s) (resumed k s) := by
  dsimp only
  apply CallBoundary.deliver _ mode (locs := [.base ⟨0⟩, .base ⟨0⟩])
    (vs := [.bool true, .bool false]) rfl
  · intro l h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · exact .cons rfl (.cons rfl .nil)
  · rfl
  · exact .cons rfl (.cons rfl .nil)

-- Interior destinations remain admitted, including repeated destinations.
theorem interior_alias_writes (k : Continuation) (mode : NormalExit) :
    let ctx := ProgramCtx.ofTables (types := #[])
    let dest : Loc := .index (.base ⟨0⟩) 0
    let s : Store := {heap := #[.value (.array 1 .bool) (.array #[.bool false]),
      .value .bool (.bool true), .value .bool (.bool false)]}
    let b : CallBoundary := ⟨⟨[7, 7], LocalEnv.declare [] 7 dest, k⟩,
      ⟨"InteriorAlias"⟩, [.base ⟨1⟩, .base ⟨2⟩]⟩
    PickFreeRun ctx (b.exit mode s) (resumed k s) := by
  dsimp only
  apply CallBoundary.deliver _ mode
    (locs := [.index (.base ⟨0⟩) 0, .index (.base ⟨0⟩) 0])
    (vs := [.bool true, .bool false]) rfl
  · intro l h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · exact .cons rfl (.cons rfl .nil)
  · rfl
  · exact .cons (t := {heap := #[.value (.array 1 .bool) (.array #[.bool true]),
      .value .bool (.bool true), .value .bool (.bool false)]}) rfl (.cons rfl .nil)

#print axioms read_before_alias_writes
#print axioms interior_alias_writes
end RD3Adversarial
```
