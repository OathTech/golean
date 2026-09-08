# Next increment proposal: package-correct method identity

[AGENT] 2026-09-08. PROPOSED, following the user's firsthand request to
review current main, the master plan, unlanded worktrees and owed work and
recommend a coherent increment with high value and a clear acceptance test.
This authorizes the survey and proposal, not implementation or merge.

Survey began at main `dc83782d`. The other agent advanced main to `f54753fa`
while the survey was running; this proposal worktree branches from that tip.
I1's strict declaration boundary and the seven typed gates are now on main.
The latter's final train records remain the landing agent's work. This lane
changes only this proposal document. No prototype or landing worktree is edited.

## Recommendation

Deliver **package-correct method identity from checked Go source through
interface satisfaction and actual dispatch**: FR-31 / BUG-098, the identity
slice of master-plan-v2 W4 and a bounded part of F7. Suggested implementation
branch: `fix/package-method-identity`, from the completed current main train.

One acceptance sentence: **two private methods with the same spelling but
different declaring packages remain different throughout lowering, interface
checks, promotion and calls; Go's diagnostic text still uses the right display
name.** This removes the current whole-export guard and its three red cases.

This is my first choice for the next product improvement. It fixes a known
wrong-answer class currently protected by refusal, has an existing Go oracle
and regression corpus, and removes a measured obstacle to real library use.
It does not depend on the B7 state migration, a new supported-profile ruling,
reflection, the evaluation-order design or concurrency-model repair.

## Evidence and the important correction to the old brief

[AGENT] On the surveyed sources:

- [BUG-098](BUGS.md)
  records three cases: `multipkg/unexported-method-scope/{distinct,
  distinct-names,assert-panic}`. All three are still FAIL at frontend-export
  in the actual baseline. The intended observations are already specified:
  `true false`, `false`, and the exact missing-method panic respectively.
- `tools/nativefrontend/identity.go` still implements
  `checkUnexportedMethodScopes`; `emit.go` invokes it before publication.
  `GoLean/GoCore/Syntax.lean` still gives `MethodSig` and `MethodInfo` bare
  `name : String` fields. `Ops.concreteMethodForDynamic?` matches those names.
- The [Cedar census, section 13](2026-09-03_cedar-go-coverage-census.md)
  attributes a whole-export refusal to this guard in both schema `ast` and
  `resolved`, affecting eight library packages directly or by import. These
  are historical measurements, not a fresh Cedar run in this survey. Removing
  this obstacle does not imply that Cedar authorization runs: fmt, reflection
  and other recorded dependencies remain.
- The recently landed `Declaration.MemberId` already represents package and
  name separately. `NativeDeclaration.memberId` enforces exported/private
  package consistency, including the reviewed Unicode export classifier.
  Those semantics and tests are available on main; executable method matching
  has not adopted them. The declaration channel alone grants no callable body
  or complete runtime method set.

The old BUG-098 plan says to qualify method names while leaving function IDs
unchanged. **That is insufficient for promotion and interface anchors.**
`synthesizePromotionWrappers` deduplicates by `tName + "." + mfn.Name()`
(`emit.go:5977` at the surveyed tip), and `NativeToIR.decodeMethod` constructs
`recvType + "." + name` (`NativeToIR.lean:1868`). Distinct package methods
can therefore still share a wrapper or dispatch ID after a partial repair.

This is supported by an existing prototype finding, not a newly claimed
execution: the [sprint pause record](2026-09-06_typed-sprint-pause-state.md#i1--typed-i1-envelope-agent-i1_resume)
names `DefinedMix` with `p.m` and `q.m`, both receiving `main.Mix.m`.
The preserved I1 note `9ba34701:docs/2026-09-06_i1-package-envelope.md`
records that its positive fixture used anonymous aliases to avoid that
collision. The next increment must turn the defined-type shape into a
positive dispatch regression; merely reusing that easier fixture is inadequate.

The pinned Go source independently states the intended distinction:
`deps/go/src/go/types/object.go:76` qualifies private identifiers by package
path; `deps/go/src/runtime/iface.go:198` compares signatures, names and private
package paths during interface dispatch, returning the bare missing-method
name. No web or floating toolchain reference was used.

## Proposed implementation boundary

[AGENT] Freeze these requirements in a charter before implementation:

1. One explicit method-identity contract, consistent with the landed
   `Declaration.MemberId`: exported names have no distinguishing package;
   private names carry their actual declaring package. Keep display spelling
   separately accessible. Decide the small shared representation and wire
   encoding first; do not infer identity by parsing display names or receiver
   package names. A promoted method retains its original declaring package.
2. Carry that identity through interface requirement lists, concrete method
   records, called-interface maps, promoted-wrapper deduplication, interface
   anchors, method values/expressions and dispatch. Generated function IDs
   must distinguish receiver plus full method identity. Audit every producer
   and consumer of these keys, including sorting and first-missing-method
   selection for panic messages.
3. Make executable decoding reject malformed, missing or inconsistent
   identity metadata and duplicate dispatch IDs by name. Preserve the
   existing distinction between complete and exported-only method-set records:
   an unavailable private method set still cannot justify a definite answer.
4. Retire BUG-098's guard only after the end-to-end evidence passes. Update
   its static diagnostic twin and records without weakening classification
   thresholds. Preserve all executable/relation coherence obligations.

This feature includes the necessary frontend, decoder and small runtime
identity/display changes and their tests. It does not undertake the rest of
F7's TypeId grammar or function-local type policy, imported-method admission,
production I1 envelope integration, refusal-marker removal, B7, C1, native
promotion (P), or a Cedar functional driver. Existing promotion wrappers and
their recover behavior remain the execution mechanism. Any new counterexample
outside the method-identity boundary is a separately recorded finding.

## Acceptance tests: how we see it is right

[AGENT] The primary evidence must exercise the production exporter, decoder,
satisfaction checks and actual calls, not only a metadata equality helper.

| Test family | Required observation |
|---|---|
| Three existing BUG-098 cases | All become differential PASS with their current Go expectations; guard removed |
| Same spelling, different package paths (including identical package names) | Correct positive and negative interface assertions in both directions |
| One type promoting `p.m` and `q.m` | Both identities survive; each package's interface invokes its own body and returns a different sentinel value |
| Value/pointer receiver sets, embedding depth and embedded interfaces | Match pinned `go/types` membership and actual Go call results; preserve receiver adjustment and wrapper/recover behavior |
| Direct calls, interface calls, method values and method expressions | All use the same identity; no spelling-specific dispatch shortcut |
| Signatures, variadicness and Unicode names | Existing signature distinctions preserved; export/private classification agrees with the landed declaration rules |
| Wrong or missing package, duplicate identity/dispatch key, malformed record | Named refusal in the production decoder; never guessed identity or silently dropped entry |
| Missing-method panic, including multiple unsatisfied requirements | Exact pinned Go text and method selection; internal qualified keys do not leak into display text |

Generate a compact matrix of actual `go/types.Implements`/method-set answers
and compare it with the runtime answers. For admitted concrete calls, compare
distinct returned values too: agreement on interface membership alone cannot
detect two methods dispatching to one body. Use kernel-checked regression
lemmas for the changed identity/matching operations, and keep the existing
coherence and typed audit gates green. Inject a package-erasing mutation and
a wrapper-key collision to show the new controls fail for the intended cause.

Run the complete capped `scripts/ci --diff` and fresh `--slow` certification
at the candidate and required train points; decoder/wire changes engage merge
protocol 5a. Compare the twin wire before/after and explain any necessary pin
movement separately. No certified observation-set change is accepted merely
because identities were renamed. Existing baseline scope is 3,654 executable
rows (3,403 PASS / 251 FAIL) plus 394 negative PASS. The three named
FAIL-to-PASS changes, any additional improvements and born controls must be
derived and recorded; no unexplained movement or PASS-to-refusal regression.

Re-run the pinned Cedar census and report `ast`, `resolved` and `all`
individually, including any next refusal. Cost of every new standing check
and total CI must be measured. Keep evidence compact; worktree-local scratch
uses symlink overlays and success cleanup. Completion is a committed branch
with green gates and an adversarial-review handoff, followed by the ordinary
explicit merge sign-off. No implementation or merge is authorized by this note.

## Alternatives and sequencing

[AGENT] Sizes below are comparative judgment, not calendar commitments.

| Candidate | Value and acceptance boundary | Assessment |
|---|---|---|
| **FR-31 / BUG-098** | Removes a guarded wrong-answer class; identity and dispatch checked against Go; unblocks a measured Cedar export obstacle | **Recommend next. Medium feature with a clear interface.** Broader than the old one-helper description because generated IDs also collide |
| **P1 / F8: semantic certificate provenance** | Reject cached certificates after a relevant semantic/build/observer change even if wire bytes and samples agree | Best small assurance increment; high priority before major semantic refactoring. One tracked slow certificate today; both membership and confluence paths need controls. Separate it from the method-identity feature |
| **P2 / F9: frontend rejection leg** | Actual GoLean frontend rejection on negative sources; malformed executable-wire controls and required result metadata | Good medium increment. `coverage-negative` currently runs only the Go oracle; the 394 PASS count does not test GoLean rejection. The two `resultTypes[i]?.getD .int` sites remain |
| **B7: fixed ProgramCtx / heap-only Store** | Removes mutable context from the consumer state; unblocks C1 and later reasoning interface work | Highest architectural value, but a much larger migration. Preserved prototype and five customer acceptance facts are useful; reference independence, final-main rebasing and complete capture still need resolution |
| **Gate A context laws / relation bridge** | Valuable kernel-checked consumer interface | Context class still needs a precise design; relation-to-driver proof sequenced after B7/C1. Do not bundle design gates into an apparently fixed theorem assignment |
| **FloatBits correctness** | Independent, ambitious proof work with strong mathematical tests | Worth a separate proof brief, but the current master-plan brief is not executable as written: it demands `sqrt`, which FloatBits explicitly excludes and does not define. Start with an exact existing rounding/operation surface |
| **Typed-gate review follow-ups, T8.1** | Enforced check commands, Tests escape-hatch coverage, full fixtures under slow CI, old scratch cleanup | Small maintenance lane; worthwhile, particularly the reported 1.6 GB/run scratch retention, but a lower product increment than repairing method identity |

Suggested order: method identity; F8 certificate provenance (or independently
as a separately owned tooling lane if commissioned); then B7 with a new
current-main charter and a fixed reference/capture acceptance contract. F9 is
the next independent boundary-assurance feature. Keep B7's acceptance and the
BUG-090 capture limitation visible instead of treating the migration as a
routine cherry-pick.

## What is actually in the unlanded worktrees

[AGENT] Read-only `git worktree list`, per-worktree status and branch ancestry
show that the old `land/*` chunks for typed core, tooling, observer, panic
text, sprint records and I1 are already ancestors of main. The typed-gate
branch joined main during this survey. They are not a queue of unlanded
features merely because their worktree directories remain.

The three substantial paused prototypes are still dirty at their branch
heads, but **their inspected source is preserved in Git snapshots**:

| Worktree | Branch HEAD | Preserved snapshot | Files compared under GoLean / Tests / spikes |
|---|---|---|---:|
| `typed-context-store` | `ca1e01d5` | `refs/snapshots/wip-20260907/typed-context-store` = `85f9abd7` | 183 |
| `typed-i1-envelope` | `3d49e9e9` | `refs/snapshots/wip-20260907/typed-i1-envelope` = `9ba34701` | 185 |
| `typed-byte-runtime` | `35aee5d3` | `refs/snapshots/wip-20260907/typed-byte-runtime` = `84b14187` | 186 |

For every file in those snapshot subtrees, a read-only `git hash-object
--no-filters` of the current worktree file matched the corresponding snapshot
blob. No missing file or additional untracked file appeared under those three
subtrees. This does not certify generated evidence, tooling or build artifacts,
and it does not claim the snapshots are independently validated. It does
correct the master plan's assertion that this source exists only on disk.
No preservation commit or cleanup of another agent's worktree is needed for
this survey.

Their acceptance gaps remain material:

- B7: source-bound reference and machine/driver/customer migrations exist;
  the [pause record](2026-09-06_typed-sprint-pause-state.md#b7--typed-context-store-agent-b7_resume)
  withdraws V1 dependency completeness, records an unreviewed V2 boundary,
  a failed broader generated-declaration check and an incomplete full capture.
  The old before-model predates main's terminal repairs. None of these is
  resolved by the existence of a snapshot.
- I1 V2: complete envelope/query prototypes are useful source material, but
  production query connection, guard closure, runtime-error facts and marker
  removal remain outstanding. Its last recorded full gate failed; the
  already landed strict declaration slice should not be overwritten wholesale.
- Byte runtime: exact append refinement and bounded speedups are promising,
  but the original BUG-090 workload is still blocked by retained intermediate
  strings. It is not a completed solution to that performance requirement.
- `typed-uintptr-identity` remains subject to the named D1 ruling. Old
  reasoning/campaign branches remain downstream material under the repo split.

## Survey scope and record checks

[AGENT] This is a source, history and evidence review. No fresh corpus,
prototype build or Cedar measurement was run, and no old success record was
re-labeled as current certification. Sources consulted include master-plan-v2
sections 2-4, the gate audit F8/F9, BUG-098/099, the B7 design and handoff,
the sprint pause record, the I1 package-envelope note and current source,
the typed-gate review/residuals, baseline rows and the pinned Go source.
The proposal passed documentation/link, evidence-size and AGENTS-alias
checks, and `git diff --cached --check`. Only this document is staged;
implementation will have its own charter and full gates.
