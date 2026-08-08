// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/literals.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type allTheLiterals struct {
	int uint64
	s   string
	b   bool
}

func normalLiterals() allTheLiterals {
	return allTheLiterals{
		int: 0,
		s:   "foo",
		b:   true,
	}
}

func outOfOrderLiteral() allTheLiterals {
	return allTheLiterals{
		b:   true,
		s:   "foo",
		int: 0,
	}
}

func specialLiterals() allTheLiterals {
	return allTheLiterals{
		int: 4096,
		s:   "",
		b:   false,
	}
}

func oddLiterals() allTheLiterals {
	return allTheLiterals{
		int: 5,
		s:   `backquote string`,
		b:   false,
	}
}

func unKeyedLiteral() allTheLiterals {
	return allTheLiterals{0, "a", false}
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func lit(v allTheLiterals) int {
	code := int(v.int)*100 + len(v.s)*10
	if v.b {
		code++
	}
	return code
}

func goleanLiterals() int {
	return lit(normalLiterals()) + lit(outOfOrderLiteral())*10 +
		lit(specialLiterals()) + lit(oddLiterals()) + lit(unKeyedLiteral())
}

func main() {}
