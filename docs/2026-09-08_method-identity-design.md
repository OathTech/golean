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
