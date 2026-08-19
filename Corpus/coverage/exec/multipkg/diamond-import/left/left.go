package left

import "base"

// L is initialized AFTER base (dependency order): it sees Seed = 10.
var L = base.Seed + 1
