package right

import "base"

// R is initialized AFTER base (dependency order): it sees Seed = 10.
var R = base.Seed + 2
