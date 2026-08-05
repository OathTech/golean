package main

// A bare call to a value-returning helper inside init() — BUG-012
// surfacing through the arc's own $pkginit route as "package init:
// extra GoCore assignment value" (a shape that did not exist before the
// init slice). Arc-final audit F11 (2026-08-06), red-first.

var bciN int

func bciBump() int {
	bciN = bciN + 1
	return 3
}

func init() {
	bciBump()
}

func bareCallInInit() int {
	return bciN
}
