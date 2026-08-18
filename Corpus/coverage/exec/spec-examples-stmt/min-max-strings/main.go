package main

// spec#Min_and_max block Min_and_max-4-c767f355: "For string
// arguments the result for min is the first argument with the
// smallest (or for max, largest) value, compared lexically
// byte-wise":
//   min(x, y)    == if x <= y then x else y
//   min(x, y, z) == min(min(x, y), z)
// Expected: min("foo","bar") == "bar"; the manual if-form agrees on
// every pair tried (including equal strings and a prefix pair, where
// "ab" < "b" byte-wise and "a" < "ab"); the 3-argument form equals
// the nested 2-argument form; max mirrors min.

func mmsManualMin(x, y string) string {
	if x <= y {
		return x
	}
	return y
}

func minMaxStringsPair() (string, string, bool, bool, bool) {
	pairs := [][2]string{
		{"foo", "bar"},
		{"bar", "foo"},
		{"same", "same"},
		{"a", "ab"},
		{"ab", "b"},
		{"", "x"},
	}
	agree := true
	for _, p := range pairs {
		if min(p[0], p[1]) != mmsManualMin(p[0], p[1]) {
			agree = false
		}
	}
	return min("foo", "bar"), max("foo", "bar"), agree,
		min("a", "ab") == "a", min("ab", "b") == "ab"
}

// N3 note (completed at the delta-review F-8): the spec states the
// associativity identity for min, "for numeric arguments"; for STRING
// min AND max alike it is a mathematical consequence of the total
// order plus gc-verified behavior, not a quoted spec clause.
func minMaxStringsAssoc() (string, bool, string, bool) {
	x, y, z := "foo", "bar", "baz"
	m3 := min(x, y, z)
	x3 := max(x, y, z)
	return m3, m3 == min(min(x, y), z), x3, x3 == max(max(x, y), z)
}

func main() {
	minMaxStringsPair()
}
