// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/repeat_vars.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func ifJoinDemo(arg1, arg2 bool) {
	arr := []int{}
	if arg1 {
		arr = append(arr, 2)
	}
	if arg2 {
		arr = append(arr, 3)
	}
}

func repeatLocalVars() {
	g := 0
	{
		a := 2
		g = a
	}
	{
		a := 3
		g = a
	}
	if g != 3 {
		panic("failure")
	}
}

// --- GoLean harness ---
// Authored wrapper.

func goleanRepeatVars() int {
	ifJoinDemo(true, true)
	ifJoinDemo(false, true)
	repeatLocalVars()
	return 1
}

func main() {}
