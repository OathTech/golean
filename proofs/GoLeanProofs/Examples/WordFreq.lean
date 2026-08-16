import GoLeanProofs.Examples.WordFreq.Pure
import GoLeanProofs.Examples.WordFreq.Machine
import GoLeanProofs.Examples.WordFreq.Build
import GoLeanProofs.Examples.WordFreq.Scan
import GoLeanProofs.Examples.WordFreq.Scan2
import GoLeanProofs.Examples.WordFreq.Scan3

/-!
# WordFreq — umbrella

The wordfreq gallery unit's proof shards: the pure specification layer
(`Pure`), the pinned program and machine vocabulary (`Machine`), the
build phase (`Build`), and the scan phase (`Scan`/`Scan2`/`Scan3`,
ending at `scan_phase` and `build_scan_chain` parked at the
count-phase seam). The count/range/assembly half is W4's.
-/
