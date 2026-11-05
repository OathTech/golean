package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-226's line): the range statement's variable-list shapes the
// corpus did not hold — a blank in the value or key slot of the `:=` and
// the `=` forms, the no-variable form over every collection kind, and
// operands that are a conversion, a literal, a constant string, a reslice
// or a nested element; a range in a generic body and in a closure.
// Expected = gc go1.26.5.

// A20.2
func sliceKeyBlankValue() int {
	s := []int{7, 8, 9}
	n := 0
	for i, _ := range s {
		n += i
	}
	return n // 3
}

func sliceBothBlankAssign() int {
	s := []int{7, 8, 9}
	n := 0
	for _, _ = range s {
		n++
	}
	return n // 3
}

func mapBlankAssign() int {
	m := map[string]int{"a": 1, "b": 2}
	n := 0
	for _ = range m {
		n++
	}
	return n // 2
}

func stringKeyBlankAssign() int {
	var i int
	n := 0
	for i, _ = range "héllo" {
		n += i
	}
	return n*10 + i // (0+1+3+4+5)*10 + 5 = 135
}

func arrayAssignValue() int {
	var i, v int
	arr := [3]int{4, 5, 6}
	n := 0
	for i, v = range arr {
		arr[2] = 100 // the range copies the array: v stays 6
		n += v
	}
	return n*100 + i*10 + v // 1500 + 20 + 6 = 1526
}

func intAssignKey() int {
	var i int
	n := 0
	for i = range 4 {
		n += i
	}
	return n*10 + i // 60 + 3 = 63
}

func stringRuneAssign() int {
	var c rune
	n := 0
	for _, c = range "ab" {
		n += int(c)
	}
	return n*1000 + int(c) // 195000 + 98
}

// A19.6
func rangeSliceNoVar() int {
	n := 0
	for range []int{1, 2, 3} {
		n++
	}
	return n // 3
}

func rangeStringNoVar() int {
	n := 0
	for range "héllo" {
		n++
	}
	return n // 5 runes
}

func rangeMapNoVar() int {
	m := map[int]int{1: 1, 2: 2}
	n := 0
	for range m {
		n++
	}
	return n // 2
}

func rangeArrayNoVar() int {
	n := 0
	for range [4]int{} {
		n++
	}
	return n // 4
}

// A20.5
func rangeBytesConversion() int {
	n := 0
	for i, b := range []byte("héllo") {
		n += i * int(b)
	}
	return n
}

func rangeSliceLiteral() int {
	n := 0
	for _, v := range []int{1, 2, 3} {
		n += v
	}
	return n // 6
}

func rangeStringConstant() int {
	const s = "abc"
	n := 0
	for i, c := range s {
		n += i + int(c)
	}
	return n // 297
}

func rangeMapLiteral() int {
	n := 0
	for k, v := range map[int]int{1: 10} {
		n += k + v
	}
	return n // 11
}

func rangeReslice() int {
	s := []int{1, 2, 3}
	n := 0
	for _, v := range s[1:] {
		n += v
	}
	return n // 5
}

func rangeNestedElem() int {
	m := map[string][]int{"a": {1, 2, 3}}
	n := 0
	for _, v := range m["a"] {
		n += v
	}
	return n // 6
}

// A20.10
func sumG[K comparable, V int | float64](m map[K]V) V {
	var s V
	for _, v := range m {
		s += v
	}
	return s
}

func rangeInGenericMap() int {
	return sumG(map[string]int{"a": 1, "b": 2}) // 3
}

func rangeInClosure() int {
	f := func(s string) int {
		n := 0
		for _, c := range s {
			n += int(c)
		}
		return n
	}
	return f("ab") // 195
}

func main() {
	println(sliceKeyBlankValue(), sliceBothBlankAssign(), mapBlankAssign(), stringKeyBlankAssign(), arrayAssignValue(),
		intAssignKey(), stringRuneAssign(), rangeSliceNoVar(), rangeStringNoVar(), rangeMapNoVar(), rangeArrayNoVar(),
		rangeBytesConversion(), rangeSliceLiteral(), rangeStringConstant(), rangeMapLiteral(), rangeReslice(),
		rangeNestedElem(), rangeInGenericMap(), rangeInClosure())
}
