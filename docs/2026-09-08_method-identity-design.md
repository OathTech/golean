# Package-correct executable method identity

[AGENT] 2026-09-08–09. Design and stage records for the
[charter](2026-09-08_method-identity-charter.md). Base main `f54753fa`;
implementation branch `fix/package-method-identity`. No merge or push.

## Shared identity boundary

[AGENT] The core's `MethodSig.id` and `MethodInfo.id` are I1's
`Declaration.MemberId`, containing exactly the source member spelling and
its declaring package identity. Exported members have an empty package;
private members carry the original checked object's import path. Go's
existing I1 `declarationObjectName` constructor now returns a comparable
`memberID` record and supplies both declaration and executable wires.
There is no executable-specific export classifier or identity field.

Executable requirements and all four method shapes (ordinary body,
promotion wrapper, interface anchor, quarantined signature stub) replace
`name` with the required `id: {name, package}` object. The checked `types.Func`
is retained when recording an interface call for later anchor synthesis.
The shared `NativeDeclaration.decodeMemberId` enforces the same exact keys,
nonempty name, and Unicode export/package agreement in both consumers.
Duplicate full interface member identities are refused without reordering.

The production wire still identifies as `golean-native-v1`, consistent with
the earlier required-field migrations. Old bare-name method records are
rejected at decode; there is no compatibility fallback. Sharing the member
decoder does not connect the separate I1 declaration envelope to executable
demand and does not claim production raw duplicate-JSON-key validation.

Core record equality compares the full identity, with its soundness proofs
updated. Bare display spelling is always projected from the record. The
first stage deliberately leaves guarded matching and target-function keys
at their existing name-based behavior; it is a representation migration,
not the BUG-098 fix. The guard survives until all three stages are complete.

## Stage 1 pin reason

[AGENT] A fresh twin emission changes 537 method records and 28 interface
requirements from bare names to I1 member objects. Of the methods, 132 are
private; none of the 28 requirements is private. Replacing each new id object
with its name reproduces the entire previous parsed wire, including all
other fields and array order. The old twin SHA-256 is
`758110a3f5a212b8138d5c4ce88fd1b1b62bee35760c289d47157fe1a1e573c7`;
the fresh SHA-256 is
`a225ea8a40a78dc3e83241520706f6a85e0675cdedab49de2b5f973ca0c7a46c`.
The I1 declaration fixture stays byte-identical (24 types / 576 Go identity
pairs), including its pin. Full differential and slow evidence is required
before committing this twin re-pin; any certified-set change is a finding.

## Validation controls

[AGENT] `scripts/check-method-identity` is an explicit CI library step.
It compiles two kernel record-equality regressions, emits a fresh Go fixture
through the ordinary frontend and decodes it through `NativeToIR`, checking
ordinary/promoted/interface identities across ASCII, accented, title-case
and supplementary Unicode identifiers. Negative wire inputs are rejected by
both path and cause. The post-import audit checks every local GoLean/Tests
constant, including unused/private declarations, and is tested with compiled
private axioms in the shared member decoder, executable decoder and audit,
and a compiled proof hole in the test module. It uses the landed symlink
overlay helper; successful scratch is deleted, failures retain a reason.

The first full pre-pin run exposed an old hand-built eval wire using a bare
`Lock` requirement. Adapting that fixture to the required id object preserves
its two existing assertions: no coverage record refuses; a full empty record
answers the definite no. This is a schema-fixture adaptation, not a changed
assertion or a semantic regression.

## Cedar measurement scope

[AGENT] A fresh before census, with the guard still enabled and the same
pinned Cedar sources, confirms 17 static declaration findings: eight methods
plus one interface in schema/ast, seven methods plus one interface in
schema/resolved. The historical text's arithmetic “9 + 7 methods + 2
interfaces = 17” is inconsistent; nine is ast's declaration total.

The eight affected entries in the combined static package report include
synthetic `main`. Restricting that report to the historical Cedar-go scope
(excluding the two k8s packages) gives 8/24 entries, with the constraints
stand-in and synthetic driver included. This is not eight independently
refused Cedar package exports. In the 22 standalone Cedar library cases,
18 export and four hit the guard: schema, schema/resolved, schema/validate,
and x/exp/types. schema/ast alone exports already. `all` and the validate
driver also hit the guard. Final evidence will separate these units and
compare the same fresh cases after guard retirement.

## Stage 1 initial measurement

[AGENT] The full pre-pin `scripts/capped scripts/ci --slow` completed in
1,368.006 seconds (exit 1, recorded; inherited cache with the changed
closure rebuilt). All 3,654 executable results/stages and all 394 negative
results match their existing baselines. Fresh slow enumeration certifies
6,193,933 nodes / 6,565,663 edges and the unchanged six observations; its
wire hash is unchanged because that case has no affected method records.
The new standing identity step costs 18.936 seconds in this run. Failures
are the old twin pin, the two eval assertions blocked by their old fixture
schema, and the resulting failed eval library receipt. Full evidence:
[initial run](evidence/2026-09-08_method-identity/stage1-before-repin.json).
The corrected candidate owes a green full run before the stage-1 commit.

## Stage 2 — full-identity matching

[AGENT] 2026-09-09. Stage 1 source commit `ac8231fd` is exactly the staged
candidate tree `fba2bc92bc74e3b871217f9c03767f591f6d5520` that passed the
full capped `scripts/ci --slow` in **1390.100 seconds**. Its 3,654 executable
and 394 negative rows have no result/stage drift; the fresh slow run has the
same six certified observations. The source-bound receipt is
[`stage1-green.json`](evidence/2026-09-08_method-identity/stage1-green.json).

The shared concrete-method lookup now accepts `Declaration.MemberId`.
Satisfaction compares that identity and the complete signature, including
variadicness. Dispatch callers pass the same record id because there is one
lookup primitive, including race access accounting. Panic payload checks name
the exported `Error` and `String` members with empty package identity. The
complete dispatch claim still awaits stage 3's target
keys, wrapper deduplication and guard retirement. No second transitional
bare-name lookup is introduced.

Missing-method selection preserves the first unsatisfied requirement record
until coverage is decided, then renders its bare `name` projection. The
validated package field decides exported-only coverage: a nonempty package
marks a private requirement whose absence from an exported-only table is
unknown and must refuse. The previous ASCII-only classifier is removed.
Pinned Go `go/types/object.go` and compiler `types/sym.go` order interface
methods exported first, then name, then private package path; the emitter's
`Interface.NumMethods` order is already correct and is preserved.

Five kernel regressions and 1,620 runtime cells cover package/name identity,
signature shape, variadicness, and pointer/value inheritance. Additional
controls distinguish full, exported-only and absent method-set records and
require bare missing-method display, including Unicode names. The imported
audit now pins six compiled poisons, adding the core lookup and syntax modules.
The decoder and frontend BUG-098 guard are unchanged in this stage.

[AGENT] Stage 2 source commit is recorded in
[`stage2-green.json`](evidence/2026-09-08_method-identity/stage2-green.json).
The exact staged tree passed full capped CI `--diff` in **1225.624 seconds**,
with no drift across 3,654 executable and 394 negative rows. Its method step
cost **28.811 seconds**, including all six compiled audit controls. Slow-tier
observations were checked against their tracked certified set in this stage;
the frontend and decoder had no new stage-2 changes.

## Stage 3 — callable targets and dispatch

[AGENT] 2026-09-09. All executable method targets now use one derived
constructor: Go `methodFuncKey(receiver, memberID)` and Lean
`methodFuncId(receiver, Declaration.MemberId)`. The serialized internal key
is `$method$<receiver UTF-8 byte length>:<receiver><package UTF-8 byte length>:<package><name>`.
The receiver is the existing supported type key; the package/name is the
same I1 member record carried by the method and its requirements. Original
checked objects survive constrained selection and late interface-anchor
registration. The constructor is used for ordinary and generic methods,
promotion deduplication and forwarding, method values/expressions, interface
anchors, fmt adapters, and generated children of method bodies.

Injectivity on emitted keys: the reserved prefix identifies the method
namespace; the canonical decimal length and colon delimit the exact receiver
bytes, then the next length delimits the package bytes; the remainder is the
Go member identifier. Equal serialized keys therefore have equal receivers,
packages and names. Valid Go identifiers contain no `$`, so generated child
suffixes (`$lit`, `$fmt`, `$once…`, and the other fixed helper constructors)
cannot alias a real member identifier. Ordinary source function keys cannot
start in this reserved namespace under the existing admitted path grammar;
other synthetic roots use distinct prefixes. The decoder retains its whole
function-table duplicate-id rejection for forged wires. This is an internal
callable-target encoding derived from I1 identity, not another member schema
or a Go-visible type spelling. Go and Lean pin the same Unicode vector:
`main.Δ` / `p.é` → `$method$7:main.Δ1:pé`.

The receiver has two necessary wire views: `recvType` determines the target
key and `recv.type` determines method resolution. Their historical unchecked
duplication (J-37) is closed at the decoder: the outer receiver key must agree
with the decoded named-type index, interface key or modeled sync kind, with
the supported single pointer layer. Named malformed controls swap either
view and exercise pointer/interface/sync shapes. This does not claim full Go
typing or redesign TypeId; it prevents these two dispatch identity channels
from disagreeing.

Promotion remains the current frontend wrapper implementation. In the future
G-P design, the method-set record still names the original member independently
of its receiver path. Native path resolution can return the same derived
callable targets or ordinary declaring-body targets, so G-P can replace
wrapper construction without changing member identity or display semantics.

The init-quarantine graph and raft graph readers also key interface expansion
by full member identity. Receiver/signature expansion remains conservative.
Raft tooling resolves legacy entry/display labels from records, refuses an
ambiguous private label, and uses receiver records for source lookup and
imported-stub classification; it never parses the new target as a Go display.
The lowerdiag method listing remains source-declaration display (promotion
wrappers and interface anchors are excluded there).

The BUG-098 whole-export guard and its static diagnostic twin retire only in
this final stage. Its historical dynamic cause text stays as a regression
tripwire. Eight new differential rows cover actual distinct results through
promotion, nested/aliased receivers, embedded interfaces, pointer method sets,
generic methods and closures, Unicode, method values/expressions and constrained
calls. The three original BUG-098 observations and expected panic text are
unchanged. The standing method gate executes the fresh wire with the production
CLI, checks graph separation, and pins two compiled producer corruptions:

- Erasing private package identity: compilation and export succeed; production
  decode rejects `.id: unexported member has no package identity`.
- Collapsing only promotion deduplication to a bare member name: compilation
  and export succeed; execution rejects `dynamic type main.Mix has no method m`.

These behavioral controls complement six compiled audit poisons (unused
private axioms and a proof hole, rejected by declaration name). Successful
scratch is removed, dependencies are symlinked, and failed scratch keeps its
cause and subprocess logs. Re-certification cost and full-run drift are
recorded below before any final source commit.

[AGENT] The first full stage-3 run caught five existing PASS→stuck regressions:
`fmt/fprint-writers/{buffer-single,builder-single,fprintf-buffer-shape}` and
`fmt/fprintf-builder/{describe-shape,returns}`. The writer-selection helper
still returned literal `strings.Builder.WriteString` / `bytes.Buffer.WriteString`
targets. It now resolves the checked `WriteString` method object and uses the
same member/target constructors. No baseline or expected observation was changed
to accept these failures. The recorded initial run was 540.596 seconds, with all
three BUG-098 rows and all eight new controls green, and the unchanged slow set;
[`stage3-initial-full.json`](evidence/2026-09-08_method-identity/stage3-initial-full.json).
A new Go graph control also pins that an unrelated private quarantine cannot
poison package initialization, while the matching member's quarantine does.

## Stage 3 pin reason and complete measurement

[AGENT] The corrected full differential/slow run took **543.844 seconds**.
Its process exit is 1 because the remaining 248 designed-red baseline cases
are FAIL. The complete comparison establishes exactly three original BUG-098
FAIL→PASS flips and eight new PASS rows: **3662 = 3414 PASS / 248 FAIL**.
There are no PASS→non-PASS changes, removed cases, or other result/stage drift;
all 394 negative cases match. The fresh slow graph again certifies the same
six observations, 6,193,933 nodes and 6,565,663 edges. The corresponding baseline
update preserves every existing alternation and its reason block.

The fresh twin changes exactly **1,316 call targets and 46 generated child
function names**. Each changed value decodes back to its old receiver/name
form; all other values, structure and ordering are unchanged. Its SHA-256
moves from `a225ea8a40a78dc3e83241520706f6a85e0675cdedab49de2b5f973ca0c7a46c`
to `13d8b659b115a68f62d47ece7654ebb1baf0de4dd8c72b3b26fee09621e9eb04`.
The I1 declaration fixture and the slow wire/set pins remain unchanged.
The source-bound record precedes both updates:
[`stage3-before-repin.json`](evidence/2026-09-08_method-identity/stage3-before-repin.json).
Full capped CI with fresh slow certification is still required before the
stage-3 source commit; final clean-source evidence follows that commit.
