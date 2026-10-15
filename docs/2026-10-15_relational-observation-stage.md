# O1 semantic observations

[USER] 2026-10-15: undertake O1 under the relayed observation charter from
audited I1 implementation `5d8e53e9f1a046fb645fce49901de714591e0819` and
handoff `b647476a44e5ffd408e1fdf6a6591be71810fefb`. Preserve observer behavior,
existing acceptance and immutable inputs. Relay constraints through the user;
no main merge, push, live repin, peer writes or global changes.

Frozen customer input is logic `f314a4f7ce69f8e5dc1c835298d4f1a2832a996f`,
reviewed handoff `97426cab7c87ca52a5e3c480c9cb9b30ac534dde`. Original and
experimental observation definitions are read from immutable git objects;
private extracts live in this lane's disposable scratch. The later frozen RD8
constraint input and acceptance are recorded below.

## Semantic census and review

The existing seven `EntrySite` introduction cases and discarded-result exit
laws do not prove the complete operational census. Moving or comparing their
source tables alone would leave that obligation open.

[AGENT] 2026-10-15: use an independent structural account of the actual call
frames, together with the exact entry-funnel and result-snapshot equations,
to connect observations to actual frame pushes and normal pops. An early
independent review (O1-R1) identified that decorated-rule erasure/coverage alone
would also hold for an incorrect all-empty decoration. The implementation must
therefore prove the structural effects of the other rules and their helpers,
including helpers that return configurations. A duplicate decorated rule table
was explored in scratch; it is not the completeness argument.

The structural extraction ignores administrative frames, not function frames.
Deferred-chain mutation and recovery must preserve the active call-frame list.
A deferred body entry pushes a frame even during panic unwinding; a plain panic
frame pop is distinct from normal return. Target exits snapshot results before
later target evaluation/writeback, without requiring that later work to succeed.
Panic-printing helper returns and discarded `[]` payloads remain included.

O1-R1 is **fixed** by the independently checked structural effects and the
public depth iff laws, together with exact descriptor introduction/elimination.
The first reviewer accepted the structural repair; a fresh finished-implementation
review independently checked the complete interface and frozen observer bridge.
No new semantic or compatibility defect was found. The reviewed handoff records final immutable source binding and CI inspection.

## Trust and validation scope

Semantic event payload/timing, frozen observer agreement, compiled renderer
correspondence and live trust-artifact migration are separate claims. I1's 16
implementation findings remain individually open and unwaived. In particular,
opaque Ty/GoValue/Expr renderers reached by `preprintDispatch`, `unseqAtom` and
`valueEq` remain relevant to exact executed printing/diagnostic correspondence;
event completeness alone does not settle them.

All builds/checks use `capped`, `LEAN_NUM_THREADS=2`, and lane-local temporary
state. Preserve RD5–RD7 and D1 controls, the inherited Memory warning and the
recorded live **35 NOT-PUBLIC** failure. I1 evidence is historical, not a fresh O1 validation. Fresh O1 results are
recorded below, including the subsequently relayed exact RD8 request. The frozen
observer, RD5–RD7 consumers and RD8 guarded/prefix consumers are checked separately.

## Checked semantic statements

All names below are exported by `GoLean.Relational`, under
`GoLean.GoCore.Relational` (the `Boundary` prefix is explicit):

| Export | Exact scope |
| --- | --- |
| `Boundary.invocation?_iff` | Candidate invocation iff an `EntrySite` witnesses the exact supplied arguments and continuation. This inventory law alone is not the census proof. |
| `Boundary.entry?_iff`, `entry?_on_transition` | Exact resolved entry payload iff `Enters`, existentially or on the actual supplied transition. |
| `Boundary.ExitSite`, `Boundary.Returns`, `.transition`, `.all_successors` | Three operation-backed exit forms times falling/explicit return: discarded `[]`, general result snapshot before target delivery, and single preprint result. Every form has its exact successor and full pick-free label. |
| `Boundary.return?_iff`, `return?_on_transition` | Exact return descriptor iff an actual normal exit, including actual successor/label. |
| `step_boundary_effect`, `Transition.boundary_cases` | Every original `Step` is either an activation push with entry event, a normal pop with return event, or no event with preserved activation list or exact panic-unwind pop. Proof eliminates original rules and proves effects of all configuration-producing helpers. |
| `Boundary.entry_iff_depth` | On every successful transition, an entry exists iff active-call depth increases by one. |
| `Boundary.return_iff_depth` | On every successful transition, a normal return exists iff depth decreases by one and source control is not panicking. |
| `Boundary.History.coverage`, `.erase` | Generic projected histories exactly cover fuel-free `Run`; no terminal/safety premise. |
| `Boundary.History.append_iff`, `.split`, `.unique` | Chronological append/split and uniqueness for the same supplied initial state and complete labels. |
| `Boundary.History.realize`, `.on_prefix` | Realization with any residual choice tape and unique history for every actual executable prefix. |

The seven entry arms preserve raw supplied captures/arguments and resolved `f.id`.
Promotion/dispatch redispatch and delivered entry panic are not body entries.
A normal return after a deferred body is included even when its outer continuation
resumes a panic. Driver readback is separate. Result snapshots preserve interiors,
aliases and arbitrary values; no result typing or later-target success is assumed.
States remain unrestricted. `activeCalls` examines every control constructor and
actual `Frame.frame` cells, independently of the observation table.

`Tests.RelationalObservations.pure_return_observable` checks that a pure step with
an empty base label can have a return event. No observer-silence inference is added.

## Unchanged customer projection

The isolated client `experiments/2026-10-15-observation-compatibility/O1Compatibility.lean`
imports only the upstream facade plus frozen customer input. It is not in the
upstream default build or public dependency closure.

- `sites`: old `CallSite` iff upstream `EntrySite` (including direct empty-array admission).
- `candidate`: exact old table filtered by `CallSite`, including rejection of spawn sites.
- `entry_projection`, `return_projection`, `emit_projection`: equality to the unchanged
  observer on **all** supplied contexts/stores/controls/tapes, with arbitrary designation
  and store-sensitive call/return projections. This equation does not assert execution
  of a failed attempt.
- `history`: for every actual `Prefix`, `Boundary.History` carries exactly the unchanged
  `Safe.Obs`, with the same complete labels and endpoints. No fuel/safety premise added.

All ten original-package Observation declaration bodies (`callEntry?`, `Enters`,
`entered?`, `frameExit?`, `exitValues`, `returnSite?`, `entryEvents`, `returnEvents`,
`emit`, `Silent`) are byte-identical to the frozen experimental bodies. `CallSite`
is also byte-identical; entire `FrameCont.lean` and `Observer.lean` files match.
This connects the compiled experimental bridge to the original definitions without
building or editing the live package. The original observation module's stale
census commentary is not relied on as a proof. The fresh reviewer independently
verified these source agreements and compiled the bridge against its own O1 outputs.

## Executed renderer correspondence: precise remaining obligation

No old operational function or generated renderer was changed. O1's kernel theorems
relate the existing operation constants, exact event payloads and pre-stores; they
supply no new equality between an opaque logical constant and its compiled body.
The all-state observer equality is a mathematical equality of the frozen definitions,
not a theorem about native execution of either projection.

A fresh value-dependency probe finds:

| Root | Unresolved generated representation endpoints |
| --- | --- |
| `Boundary.entry?`, `Boundary.return?` | `GoLean.instReprGoValue.repr` |
| `preprintDispatch` | `GoLean.instReprGoValue.repr` |
| `unseqAtom` | value and `GoLean.GoCore.instReprExpr.repr` |
| `valueEq` | value and `GoLean.GoCore.instReprTy.repr` |
| `stepFn`, `stepMulti`, `runProgramM` | value, expression and type printers |
| `Config.abort?`, `raceUpdate` | no such endpoint reached by this probe |

The probe follows kernel-visible bodies and stops at opaque endpoints. Thus the
empty rows do not establish absence of hidden compiled dependencies. In particular,
`Boundary.return?` reaches value rendering through the failure branches of
`loadResults`/`Mem.loadBinding`; `Boundary.entry?` reaches it through `enterFrame`.
Preprint dispatch's malformed unboxed-payload refusal embeds `repr other`.
`unseqAtom`'s non-atom rejection embeds the expression printer. `valueEq` embeds
value/type representations in rejection diagnostics. All-state error/printing
correspondence must preserve those exact strings, not just the error tag.

The bounded follow-up contract is: for each reachable Ty/GoValue/Expr generated
printer, every finite input and precedence, and every formatting width/indent used
by its callers, execution of the pinned generated implementation terminates with
exactly the formatted output of a total, kernel-visible specification. Mutually
recursive and nested representation dependencies must be included. Those total
constructor equations must then compose through the unchanged diagnostic callers,
including preprint dispatch/abort refusals, unseq rejection and equality rejection,
to preserve the complete `Stop` payload and observable output. This is an executed
implementation correspondence obligation, not the unsupported kernel equation
`totalPrinter = oldOpaquePrinter`: Lean supplies no defining equations for that
old opaque value. A behavior-preserving replacement needs an explicit generated-code
correspondence argument and checked total equations, with its trust basis stated;
finite controls or a green axiom audit alone cannot discharge it.

That obligation remains **open and blocks exact executed renderer correspondence
and the full replacement landing claim**. It does not weaken or add safety premises
to the checked successful-step semantic census. All 16 inherited D1 findings retain
their individual open dispositions in the I1 stage; no printer/equality/seed or
Declaration representation finding is waived by O1. RD8's actual observed-caller completion and live
trust-artifact migration remain separate, as does U1 and any later combined pin.

## Validation

- Facade build and new semantic clients: PASS, warning-free; all twelve headline
  theorems report standard axioms only.
- Frozen RD7 build: PASS, all 6,058 local declarations standard axioms; unchanged
  closed original program acceptance, including its downstream initialization proof.
  Exact kernel replay: PASS, 411 modules exactly once: 100 GoLean, 65 RelationalCodeX,
  34 GoLeanIris, five examples, one O1 bridge, 174 Iris, 18 Batteries, 14 Qq.
- O1 compatibility: PASS, both headline theorems and exhaustive 58-declaration
  audit use only the standard trio; the independent reviewer repeated both checks
  and the exact single-module replay using its independently rebuilt O1 outputs.
- Frozen RD6 original-header build: PASS, including `C2Adapter`, `C2Acceptance`
  and `OriginalAcceptance`, with explicit downstream `InitAssembly`. Original
  aggregate: 5,940 local declarations; acceptance aggregate: 5,943, standard trio.
  Exact kernel replay: PASS, 407 modules exactly once: 100 GoLean, 59 RelationalCodeX,
  34 GoLeanIris, five examples, three original acceptance clients and the same
  206 dependency modules. All 100 upstream `.olean` files are byte-identical to
  those in the root build; the private replay is of the actual changed closure.
- All 113 RD7 and 106 RD6 original package files match immutable input objects,
  except private pin/added Lake targets. All original Lean files are unchanged.
  Four clean exact independent clones per package; no alternates or writable cache links.
- D1 archived-C1 comparator/shadow/detector preservation: PASS, complete output
  byte-identical. D1 build: PASS (83 jobs). Exact replay: PASS for eight experiment
  modules plus five facade/audit clients (13 total). Fresh D1 exhaustive axiom audit:
  22,310 declarations, standard trio only. Separate implementation scan: **FAIL,
  16 inherited findings**, unchanged and unwaived.
- Full current-main `scripts/ci --diff`: **PASS**, 2,115 seconds; 235 build jobs,
  warning-free; exact replay of all 100 GoLean modules; exhaustive core axiom audit;
  396 interpreter tests; frontend, boundary and whole-tape scheduler checks. Fresh
  differential: 4,025 cases, 3,767 PASS and 258 tracked FAIL. Fresh negative:
  415/415 PASS. Full baseline comparisons show no regression or cause drift;
  both baselines remain unchanged. All speedbumps pass.

CI correctly reports a dirty precommit tested tree, not an exact-commit invocation.
The handoff binds its 4,353 code/configuration/script/corpus source hashes to the
implementation commit. All 100 GoLean `.olean` bytes match those used by the
complete private replay. No production operational function was edited.

The reviewed handoff records the immutable pin and source binding. RD8's actual observed-caller completion and live trust-artifact migration are not
claimed. Reproduce using the compatibility experiment README and the I1/C2 recipes
it names; no permanent export imports a downstream module.

## Exact RD8 acceptance

[USER] 2026-10-15: consume frozen logic checkpoint
`5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42` under the relayed RD8/O1 constraint;
retain independent semantic completeness, immutable sources and private builds.
The frozen checkpoint records passing author checks but pending result review,
and its actual observed caller remains unfinished. Those statuses are not
upgraded by this upstream delivery.

`experiments/2026-10-15-observation-compatibility/RD8Acceptance.lean` supplies:

| Exact frozen obligation/use | Checked adapter |
| --- | --- |
| `RelationalCodeX.Observed.EventAgreement events` | `RD8Acceptance.agreement` |
| `prefix_acceptance events agreement` | `RD8Acceptance.prefix_history` |
| `observed_step events agreement` | `RD8Acceptance.guarded` |

`events` maps public `BoundaryEvent.entry/returned` to the frozen sum constructors.
It is derived from the public semantic projection, not from legacy `emit`.
Agreement uses the separately checked all-state observer equality; completeness
remains the independent `Step` elimination/activation-effect theorem.
`guarded` restates the verbatim `LiftingTarget` body with only its agreement
parameter supplied. It retains validity, heap update, pick freedom, actual labels,
nonterminal/init admission, heap growth, invariant and later/history ownership
premises. No Iris rule or observer type is imported into public exports.

The original `original_closed_program_prefix` and
`original_closed_program_outcomes_hist` headers compile unchanged, including
StringPlain, ReturnSilent, setup, fuel and tape premises where originally present.
The private full RD8 build passes (431 jobs); the unchanged aggregate audits
6,407 local declarations, standard trio only. All 125 frozen input files match,
except private GoLean pin and appended library targets. No original Lean source
was edited; all four dependencies are clean independent exact clones. Exact kernel replay passes for all 423 modules, each once: 100 GoLean,
117 local including two adapters, and 206 dependency modules. Both added modules
pass exhaustive axiom audit (65 declarations); four direct proof edges confirm
that the prefix and guarded consumers use the supplied agreement. The fresh
review independently rebuilds and replays the adapter and original headers,
checks unchanged premises, and reports no new finding.

The aggregate's existing conditional U1 consumers are retained unchanged; their
`SimulationLaw` is not supplied here. The actual observed caller and its ownership
proof remain downstream work. This is O1-A plus its exact guarded/prefix acceptance,
not RD8-O/U completion or live census migration.
