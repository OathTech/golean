package alpha

import "reclog"

// Within a package: variable initializers run before init()
// (spec §Package initialization) — mark 1 lands before mark 2.
var A = reclog.Push(1)

func init() {
	reclog.Push(2)
}
