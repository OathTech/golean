# Independent recovery static promotion review

[AGENT] `typed-preflight`, 2026-09-06. **Bounded PASS** for the four-file
public promotion in `typed-consumer-sprint`: `GoLean/Interface.lean`,
`Tests/InterfaceAudit.lean`, and `scripts/check-interface{,.py}`. This is a
source/mechanical and gate-evidence review, not a repeated full static
judgment audit, native differential run or recovery runtime proof.

All seven `GoLean/GoCore/Recovery*.lean` modules and five
`Tests/Recovery*.lean` modules are byte-identical to reviewed static commit
`e8a665e9`; `comparison.json` records each hash. The public facade imports
the actual admission module and accurately limits its claims to a bounded
static profile, independent judgment/checker correspondence, complete
signatures/bodies and call/capture vectors, deferred registrations, and a
finite call-graph certificate. It explicitly leaves setup, runtime safety,
renderer success and Iris ownership open. The surface/placement checks are
proved consequences in the unchanged implementation; the promotion does
not narrow or redefine the admission predicate.

The interface audit requires all twelve new origins and seven exact theorem
exports. Its constant sweep remains by every imported local `GoLean`/`Tests`
origin, including unused/private/generated/trailing declarations, with the
same allowed axiom trio and forbidden customer dependency check. The shell
fresh-elaboration list and Python external audit imports include all twelve
modules. New source bytes enter the fingerprint. The three new compiled
poisons cover private diagnostics, private admission and a trailing static
test theorem; all twelve earlier poison controls remain, for fifteen total.
Each poison must compile before an external post-import audit rejects it
with the expected axiom marker; compiler failure cannot masquerade as audit
success.

The dedicated recovery audit/gate is unchanged from `e8a665e9`. Its
all-imported-local origin sweep and separate compile-then-named-reject
mutation procedure remain intact. No narrow export-only audit replaces it.

The coordinator's fresh, already-completed public interface section records
**72 required exports, 13,328 checked constants and all fifteen named
negative-control rejections**, followed by PASS. Its exact completed prefix
is retained as `interface-completed.log`; the surrounding ordinary CI was
still running at review time, so this report makes no terminal whole-CI
claim. The reviewer did not rerun the expensive gate. Static gate evidence
from the original increment remains attributed to that source/author.

No promotion defect found within this scope. Runtime/customer obligations
remain governed by the recovery claim ledger. The four promotion source
files, source comparisons and completed interface evidence are sealed by
`SHA256SUMS`.
