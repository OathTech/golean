package dn

import "rec"

// dn sorts AFTER dm but is ready at step one (dm waits for zdy), so it
// records FIRST.
var V = rec.PushD(2)
