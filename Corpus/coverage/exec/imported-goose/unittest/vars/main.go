// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/vars.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func LocalVars() int {
	var (
		a int
		b string
	)
	b += "hello"
	return a
}

func LocalConsts() (x int) {
	const (
		c = 10
		d = c + 5
	)
	const e = 1 << 3
	x += c
	x -= d
	return x
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanVars() int {
	return LocalVars()*100 + LocalConsts()
}

func main() {}
