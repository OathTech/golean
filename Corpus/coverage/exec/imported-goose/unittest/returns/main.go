// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/returns.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func BasicNamedReturn() (x string) {
	return "ok"
}

func NamedReturn() (x string) {
	x = x + "foo"
	return
}

func BasicNamedReturnMany() (x string, y string) {
	return "ok", "blah"
}

func NamedReturnMany() (x string, y string) {
	x = "returned"
	y = "ok"
	return
}

func NamedReturnOverride() (x string, y string) {
	for {
		x := "unused"
		x += "stillUnused"
		y = "ok"
		break
	}
	return
}

func VoidButEndsWithReturn() {
	// translation should not produce the value from this function call since the
	// outer function is void
	BasicNamedReturn()
}

func VoidImplicitReturnInBranch(b bool) {
	if b {
		return
	} else {
		BasicNamedReturn()
	}
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

// Positional length checksum over every named-return shape.
func goleanReturns() int {
	sum := len(BasicNamedReturn())
	sum = sum*10 + len(NamedReturn())
	a, b := BasicNamedReturnMany()
	sum = sum*10 + len(a) + len(b)
	c, d := NamedReturnMany()
	sum = sum*100 + len(c)*10 + len(d)
	e, f := NamedReturnOverride()
	sum = sum*100 + len(e)*10 + len(f)
	VoidButEndsWithReturn()
	VoidImplicitReturnInBranch(true)
	VoidImplicitReturnInBranch(false)
	return sum
}

func main() {}
