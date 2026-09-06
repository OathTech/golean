# O2 terminal integration: independent additive union review

[AGENT], 2026-09-06. **Bounded acceptance of the source union.** The review
read `typed-consumer-sprint` while the integration of `f3971190` into
`39235f658326dd26a85d0e590ff9d6e1b796c3be` was pending. It wrote only this
packet in the reviewer's separate `typed-byte-runtime` worktree. The
reviewer authored neither O2's semantic/customer changes nor this union.

All 3,952 selected source hashes were independently recomputed before and
after the checks. The selected manifest SHA-256 is
`8eff45c52710b67cc22971dc0517562cc517286854279cacb4b7d9d146a2dcd3`.
Against the accepted feature's 239-input manifest, exactly eleven paths
changed: `scripts/ci`, `lakefile.toml`, and nine string-member pins. Every
other feature input, including the terminal semantic proofs and Iris
customer files, is byte-identical to the accepted feature.

Each pin's sole changed field is `binding.apparatus_sources`. All other
fields compare structurally equal to both parents, including Go/native
wire bindings, controls, semantic membership policy and oracle identity.
The reviewer independently enumerated the apparatus roots and fixed files
from the checked-in inventory policy, rejected symlinked source entries,
and hashed all 172 resulting inputs. Every pin and the recorded inventory
match that recomputation. The two new paths relative to the integration
parent are `RecoveryTerminal.lean` and `RecoveryPoolObservationTyped.lean`;
the remaining changes are the accepted facade/gate and additive union
hashes. Parent inventory sizes are 170 and 166.

The thirteen Lake libraries are the exact parent union, with duplicate
entries equal and every other TOML field unchanged. The complete CI file
is exactly the integration parent's file plus the terminal gate stanza,
and exactly the feature parent's file plus the declaration gate stanza.
Both complete stanzas retain their failure branches. The string-member,
interface, declaration and terminal gates all remain present.

No source-union finding remains. This does **not** certify the pending CI,
fresh membership certificates, customer gate, full corpus or slow-tier
recertification; their actual terminal results remain integration duties.
No Lean replay was performed for this bounded review. The earlier O2
semantic review is the authority for its unchanged proof claims.
