# Independent R1 integration union review

[AGENT] 2026-09-06, recovery_customer, read-only review of the root integrator's
candidate on `b34cee6767de3e39f064cc5c8c2214568b332e86`, incorporating accepted
R1 `819182b5898f565f2488d706ef160319453e2f1d`.

**PASS for this bounded source/union review.** All 3,923 hashes in the root
manifest were independently re-read. The manifest SHA256 is
`fe3033c822f3a5ee79f72470c072aa95bd6699ae6e3f7cb4e0dd05090ea4f5f8`.
The only differences among R1's original 184 source inputs are the two
additive integration files and nine source-inventory pins.

The parsed Lake configuration is the exact union of the two parents' 12
libraries, including both InterfaceTests inventories. All non-library
configuration, the default targets and executable are unchanged. Removing
one intact declaration gate, already present in the integration parent,
from the combined CI yields byte-identical accepted R1 CI. No prior gate,
failure branch or library is removed.

I independently enumerated the three recursive source directories and the
22 explicit apparatus paths, rather than using the author's inventory
function as the checker. All nine pins contain that exact 169-input mapping.
Compared structurally with the accepted R1 Git objects, their only changed
field is `binding.apparatus_sources`: 160 becomes 169, with nine additive
declaration/shared-helper paths and no removal. The six input categories
previously found missing in R1 remain explicitly bound. The Go source/wire,
control, toolchain, semantic parameters, subject and envelope fields are
unchanged. `review.json` records each before/after hash and source delta.

This review does not independently rerun the expensive gates or accept new
semantic behavior. The integrator's final ordinary CI and focused nine
member rows remain separate evidence. It also does not review the author's
O2 terminal/facade union; that candidate requires another reviewer.
