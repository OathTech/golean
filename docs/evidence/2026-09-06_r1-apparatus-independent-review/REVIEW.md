# R1 apparatus independent review

[AGENT] `b7_context`, 2026-09-06, at the sprint integrator's request.
Bounded final verdict: **ACCEPTED for the apparatus source reviewed at v3**.
The original 178-input candidate required changes; both source-closure
findings below are closed by the independently checked 184-input v3 delta.
This verdict does not substitute for the separate Lean/semantic review,
generic O2 theorem integration or final CI/baseline gates.

The reviewed source is the 178-input frozen candidate on
`typed-string-members` at parent `620489c9`, with exact hashes in
`candidate-source.json`. `snapshot.json` records the manifest hash and an
owned scratch copy. No author source was edited. This review covers
`tools/string_member.py`, `tools/string_member_runner.py`, their caller and
control wiring, and the raw Go panic adapter. It does not approve the Lean
renderer/theorem chain, generic O2 terminal theorem, final CI or baseline
changes; those have separate review owners and gates.

## F1 — executable entrypoint sources escape the apparatus pin

`APPARATUS_FILES` and `APPARATUS_ROOTS` omit `Main.lean` and the root
`GoLean.lean`. The former defines the shipped executable's dispatch; the
latter defines its imported source graph. In the owned candidate copy,
adding both exact original files and then changing `Main.main` to return
zero for every invocation leaves `apparatus_inventory` unchanged (154
entries). Changing the root import module also leaves it unchanged.
`unbound-entrypoint-counterexample.json` records the exact mutation and
result. This is a predicate counterexample, not an execution/conformance
claim about the mutated program.

Consequently the fresh-build gate and before/after executable hashes do
not establish the promised complete source identity: those hashes only
show that the chosen binaries stayed fixed during the run. A changed
entrypoint can build to a different fixed binary while retaining the same
apparatus source pin. Require both inputs in the fixed inventory; refresh
the source-bound pins and add missing/changed-entrypoint challenges.
Compiled checker mutations that omit either required input must reach
the intended test assertions before rejection counts.

## Checked behavior and limits

Fresh Go helper tests pass (`go-unit.log`, exit 0), including the 256-byte
raw-record matrix and fatal/exit/report-channel refusals. Six fresh Python
unit groups pass (`python-unit.log`, exit 0). The independent
`challenges.py` run has 42 records: all nine actual sidecars validate with
thirteen roles each, positive synthetic binding/witness checks pass, and
39 malformed inputs refuse. Challenges include missing/duplicated controls,
unknown keys/scope, escaping paths, missing/changed source inventories,
stale wires/toolchain/rationale, malformed later chain entries, byte/Boolean
typing, wrong member/output, forged admission/fuel/choice metadata, and
non-verdict process exits. Exact cases and causes are in `challenges.json`.
Synthetic wire/record checks are apparatus tests, never fresh frontend or
Go/Lean conformance evidence.

The production runner executes all thirteen controls afresh (eight exact
and five abort membership controls), then plain and race Go subject runs
and four concrete model choice streams. The thirteen controls themselves
use the default model stream; the four-stream claim applies to the subject.
It rechecks source inventories, pin contents and executable hashes before
issuing a certificate and accepts no saved verdict as input. The selected
message is checked against the actual model chain's head, with every chain
entry required to have string bytes and a Boolean recovered flag; Go's raw
message is intentionally not used to reconstruct type or complete payload.
Thus the relation between native subjects and their kind/byte/order
companions still depends on the explicitly reviewed fixed source argument,
not merely role names or a text match. No generic Go compiler-correctness or
all-stream termination claim follows from these concrete checks.

## F2 — embedded and runtime-read frontend inputs were omitted

The source closure follow-up found three embedded build inputs outside
the original `.go` inventory: `tools/nativefrontend/inittask-std.tsv`
(`inittask.go:63`), `stdlib-substitutions.tsv` (`stdlibsource.go:91`), and
`stdlib-overlay.tsv` (`stdlibsource.go:111`). The same frontend reads
`baselines/stdlib-pin.tsv` (`stdlibsource.go:649`) to validate library
source. These four inputs are executable frontend data, including the
header used to derive the frontend's language/oracle version, so they must
also be bound by the claimed complete source pin.

The bounded closure inspection found no further current local input in
the runner/harness/compiler source chain: the runner's only local Python
import is the pinned checker, the Go packages' current code imports the
standard library, and the Lake manifest has no packages while the Lake
configuration has no dependency declarations. Go/Lean and host tools remain
under their existing toolchain/source-pin and fresh-build gates; this
review does not invent a new proof of toolchain binaries from version
strings. Future dependencies or build-input kinds need a corresponding
inventory update and review.

## v3 repair disposition

`candidate-source-v3.json` and `snapshot-v3.json` bind the final reviewed
184-input source. All six missing current inputs are now fixed members of
the 160-file apparatus inventory. The three implementation/test/gate
deltas are retained as `.v1-v3.patch` files. The checker change adds only
the six required source paths. The test uses an independent literal list
of those paths and checks missing and changed bytes. The gate adds six
compiling checker omission mutants.

Fresh independent v3 validation passed all seven Python groups. Each of
the six omission mutants compiled and then failed the intended required
input assertions (`omission-mutations-v3.json`, six raw logs); no syntax or
import failure was counted as rejection. All nine source-bound sidecars
changed only `binding.apparatus_sources`, preserving their subject/control
sources, wire hashes, observations, scopes and rationale. The final source
recheck matched all 184 hashes (`v3-delta-verification.json`). F1 and F2 are
closed on that exact source.

The author separately reports all nine focused cases and the full apparatus
gate passing at v3; those larger runtime runs were not rerun by this bounded
review. Final full CI and the integrator's semantic/Lean review remain
separate required acceptance checks.
