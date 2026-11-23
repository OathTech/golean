# Code-only archive copy: `archive/byte-store-spike-code`

The certified byte-store spike of 2026-09-06 (`spikes/byte-store/`) with its findings notes and independent reviews: an attempt at BUG-090, the quadratic allocation cost of the association-list heap.

This branch was published on 2026-11-23 from a retired development machine.
It is a commit-for-commit copy of `typed-byte-store-consume-review` on the pushed commit `b34cee676`,
with authors, dates and messages unchanged and `docs/evidence/` held at
that base's contents: the run evidence the original commits added is not
here, so links into it from these commits are dead. Nothing outside
`docs/evidence/` differs from the original trees.

The typed-profiles lane this belongs to was parked on 2026-09-16 and not
migrated ([USER] ruling D1, 2026-10-11, in
`docs/2026-10-11_recovery-and-migration-plan.md` on `main`). It is kept
because BUG-090 was still open when it was archived and this was the only
attempt at it. No build, gate or review was run for this copy.

Documents on `main` cite the original hashes:

| Original | Here | Subject |
| --- | --- | --- |
| `539c17f7c` | `d9da647a1` | Spike certified byte element stores with exact storeLoc refinement |
| `39add7fd4` | `486962fa1` | Ignore retained byte-store spike build artifacts |
| `880c848a6` | `663373d26` | Review byte-store certificate composition and aliasing |
| `68590160b` | `2ba9eb2ab` | Measure bounded byte stores and prove consuming modifyM refinement |
| `631b883f0` | `aa6f1674e` | Independently review consuming byte-store refinement and its necessary premise |

[USER 2026-11-23] Publish the byte-store work; evidence blobs are not published.
