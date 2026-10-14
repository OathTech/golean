# RD5 A–D independent composition audit

**ACCEPT the upstream A–D batch at
`f224a6e0877bb7d2c17719d6b8475a890617d601`. No new correctness or trust defect
found.** Exact Alias closure is checked; the full Add milestone remains open.
This is an implementation audit, not permission to merge, push or live-repin.

This review follows the RD5 relay at the frozen logic handoff
`66920605c244badf346352e241089951fd57d13d`. The implementation reviewed downstream
is `b6c31fb74f8817fd3ae6d90790204e0eabbc6d80`. I inspected the semantic laws,
their underlying machine rules, unchanged requests and original targets,
result-resource transfer, lifting, guarded recursion and concrete Add use sites.
Earlier review verdicts are not premises. The isolated reviewer branch starts
at `ed9058ef04b73ac7287dd94a9bca8e4532a5eb04` and receives the eight-file frozen
source overlay before exact candidate confirmation. No peer implementation,
live pin, charter, global state, merge or push was changed.

## Semantic assessment

A exposes precisely the required split. The normal-exit step reads the entire
result list through `Readback.traced` before target-reference evaluation and
before any `storeK` effect. Both returned and fallthrough exits have proofs;
the empty case takes a real frame exit. The ordered effects relate each write's
actual input/output stores independently. No distinctness condition occurs,
and no result-read predicate survives into `OrderedWrites`. Thus repeated,
interior and result-alias destinations are admitted at the semantic interface.
The final caller tail has no admission or safety premise. `ResultSlots` is the
unchanged request's result-root restriction, not a new destination restriction.

Downstream `call_rule_results` derives result counts and root validity from
the original frame, and readback from typed owned result cells. `wp_deliver`
retains those resources through the prefix, then consumes the Results wand
once. `WritePre` threads updated destination ownership sequentially; it does
not demand duplicate simultaneous ownership for repeated locations. Alias
uses Pair's logical denotation and does not import Pair's body proof.

B supplies a continuation-uniform `ReadOnlyExpr`, definitionally the request's
path premise. The assignment evaluates its target pointer and then the RHS,
exposes one successful `storeLoc` effect and provides unconditional cleanup.
The predicate constrains every intermediate pre-write store; cleanup never
assumes it after the write. Target-frame construction remains upstream.
Existing pointer/variable assignment theorem signatures are preserved, with
their proofs now using the general laws.

C supplies actual `Step.whileStmt` entry with source admission, not reflexive
reachability. Selection, normal repetition and unlabelled continue/break/return
follow the corresponding machine rules with arbitrary bodies and tails.
Downstream `wp_while_invariant` performs Iris Löb induction and spends its later
through this entry transition before exposing recursive iteration. Invariants,
ownership, masks and refusal-sensitive WP remain downstream obligations.
Labelled exits, arbitrary observers, panic cleanup and body execution are
not claimed by this control view.

D is derived through reusable variable read, dereference, integer literal,
same-kind addition and pointer-RHS assignment. The arithmetic normalization is
the semantic `IntKind.normalize`; the exact uint64 adapter converts it to
modular BitVec addition without a bound on the contents. Both the binding slot
and pointee keep the exact request domains. The generic pointer assignment is
limited openly to `*p = rhs`; general address-former chains are not advertised.
The downstream increment retains arbitrary interior p/q ownership and framing.
This is real reuse with B and the previous assignment laws, not a new public
catalogue of compound fixture-specific expressions.

All paths retain actual transition labels and empty pick proofs. Dereference
and result-read labels come from the machine operations; they are not replaced
with pure labels. Source admission is attached to traversed sources and effect
sources only. Observer.none silence is proved by downstream lifting; it is not
silently inserted as an upstream semantic assumption.

## Completion scope

The intended upstream acceptance is A–D and unconditional exact Alias, while
preserving Pair/Set/Keep and RD4 adapters. Add's counter initialization, actual
loop entry, modular increment and specialization of the guarded invariant rule
are intermediate acceptances. There is no `AddTarget` inhabitant in the frozen
package. Full symbolic iteration, first-flag assignment, signed counter update,
comparison, zero-count/break exits and result packaging remain work for the
logic customer. Supplying this batch cannot close that milestone finding.

## Validation

All Lean/Lake jobs used `LEAN_NUM_THREADS=2` and `capped`. Bootstrap used
independent `--no-hardlinks` clones and byte copies of caches only after the
source/configuration match was checked. The GoLean baseline-to-review-base
diff is documentation only. The original 75 package files were compared
byte-for-byte with the frozen implementation; all match. In particular,
`CompositionRequests.lean` has SHA-256
`2fbf57fb4749c85820edf68e552d823f740856ac3a68e43ec30c031b542161cf`.
Lean remains 4.32.2, Iris
`e7a0a43814c4f1154ca0c8049883ca56c2288b86`, Batteries
`023ce7d62a0531e22a5331e20b587817a80d49ff` and Qq
`38d591e778f100aec9762bb582f9c7f55f50e9dc`; dependency clones are clean.

- Baseline full experimental build: PASS, 325 jobs.
- Candidate-overlay full experimental build: PASS, 328 jobs, including
  unchanged RD4 compatibility, Set/Keep, Pair, Alias and Add obligations.
- Independently written A/B/C/D adapters: PASS, exact frozen propositions.
  A converts `OrderedWrites` structurally to the frozen `WritePath`; B is
  direct application; C projects `WhileControl`; D composes the reusable
  expression laws and rewrites modular normalization to `(a + 1).toNat`.
- Unconditional original Alias, Pair, Set and Keep targets: PASS. Specialized
  counter-init, loop-entry, increment and invariant-rule wrappers: PASS.
  These wrappers remove only their A–D arguments.
- Twelve adapter/acceptance headline axiom reports: standard trio only.
  Exhaustive imported upstream/local/wrapper scan: 23,415 declarations,
  standard trio only. The changed semantic-source scan finds no `sorry`,
  project axiom, native decision, unsafe declaration, extern/implemented_by
  hook or disabled kernel checking.
- Kernel replay: PASS, exact sets and multiplicities, 361 modules total.
  Local/upstream: 86 GoLean, 34 GoLeanIris, 29 RelationalCodeX, five examples,
  one independent adapter module. Dependencies: 174 Iris, 18 Batteries,
  14 Qq. No missing, extra or duplicate replay names.

The frozen package's local-only audit drops from 5,752 declarations at the
baseline to 5,666 with the candidate. I compared exact names and defining
modules in both environments: the only change is the 86 lazily generated
`GoLean.GoCore.Machine.applyStrictOp.eq_1` through `eq_86`, now owned by
`GoLean.GoCore.RelationalExpression` instead of `RelationalCodeX.Reuse.Struct`.
No baseline audited declaration is missing. All 86 are included in the broader
upstream/local scan and GoLean replay above. This is a module-attribution
change, not lost client proofs or reduced combined audit coverage.

The independent harness initially failed because its arithmetic simplifier
list named a nonexistent lemma and its test expressions omitted GoGS binders.
Those scratch-harness errors were repaired; only the successful rerun is
reported as validation. No implementation change was needed.

Reproduce the frozen package/bootstrap and A–D/acceptance source using
`docs/2026-10-14_relational-composition-acceptance.md`. The independent harness
used the same statements under different names, importing the frozen aggregate,
and additionally enumerated every environment declaration whose defining
module root is GoLean, RelationalCodeX, GoLeanIris or GoLeanIrisExamples,
plus current-module declarations. It called `Lean.collectAxioms` for each,
rejecting anything outside propext, Classical.choice and Quot.sound.
The build/replay commands in the scratch package were:

```sh
LEAN_NUM_THREADS=2 capped lake build RelationalCodeX
LEAN_NUM_THREADS=2 capped lake env lean \
  -o .lake/build/lib/lean/AuditAdapters.olean AuditAdapters.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose \
  GoLean RelationalCodeX GoLeanIris GoLeanIrisExamples AuditAdapters
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Iris Batteries Qq
```

For the set check, compare each `replaying` name against local/upstream source
module names (including root files and the harness), and dependencies against
their built `.olean` names. Check multiplicities as well as sets. Reproduction
with the handoff's two named harness modules naturally changes that harness
count; the request/target sources and accepted guarantees remain identical.

This review does not independently rerun the entire upstream differential CI
or the logic repository's live gate. The inherited Memory unused-`h` warning
was reproduced and remains visible. The frozen handoff's live **35 NOT-PUBLIC**
failure is not cleared by this experiment. The review base predates main's
`scripts/check-kernel-replay` CI addition, so direct replay above is explicit
evidence; it must not be described as a replay performed by that base's CI.
No runtime machine, frontend, oracle pin or existing relation statement is
modified by the candidate's eight source/test files.

The immutable candidate's eight source/test files match both the frozen review
manifest and independently built clone byte-for-byte. The only additional
candidate changes are three documentation files and one memory-inventory row;
there is no other source or build-configuration change. I inspected those
documents and the new `OrderedWrites.storeLoc` inventory entry. Its
**NO EXECUTION** classification is correct: the occurrence is a Prop-level
effect premise, and the proof supplies the actual emitting store transition.
I copied that inventory into the review tree and independently reran
`scripts/check-mem-callsites`: PASS, all 86 rows. No repeated proof build is
needed for identical Lean source and configuration. Proof checks above ran on
the verified overlay, then were matched to the immutable candidate, rather
than being misreported as an earlier run on an already-existing commit.

[AGENT] 2026-10-14: accept this immutable upstream batch and its exact Alias
acceptance. Preserve the distinct downstream Add completion obligation; A–D
uptake and its intermediate Add checks do not discharge it. The review found
no further issue requiring implementation changes.
