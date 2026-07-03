package main

// Generic type aliases are supported by the active Go toolchain.
type aliasSlice[T any] = []T
type aliasSet[T comparable] = map[T]bool
type aliasPair[T any] = struct {
	left  T
	right T
}
type aliasUnary[T any] = func(T) T
type aliasLookup[K comparable, V any] = map[K][]V

func aliasSliceSum(xs []int) int {
	total := 0
	for _, x := range xs {
		total += x
	}
	return total
}

func genericAliasSliceSameType() int {
	xs := aliasSlice[int]{1, 2, 3}
	xs[1] = 20
	return aliasSliceSum(xs)
}

func genericAliasMapLiteral() int {
	seen := aliasSet[string]{"go": true, "lean": false}
	if seen["go"] && !seen["lean"] && !seen["missing"] {
		return len(seen)
	}
	return 0
}

func genericAliasStructLiteral() int {
	p := aliasPair[int]{left: 4, right: 7}
	var q struct {
		left  int
		right int
	} = p
	return q.left*10 + q.right
}

func genericAliasFuncType() int {
	var f aliasUnary[int] = func(x int) int { return x + 5 }
	return f(3)
}

func genericAliasNestedMap() int {
	table := aliasLookup[string, int]{
		"a": {1, 2},
		"b": nil,
	}
	return len(table)*100 + len(table["a"])*10 + len(table["b"])
}

func main() {
	genericAliasSliceSameType()
}
