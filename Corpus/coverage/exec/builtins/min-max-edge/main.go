package main

type minMaxEdgeInt int
type minMaxEdgeString string

func builtinMinMaxOneArg() int {
	return min(7)*10 + max(8)
}

func builtinMinMaxEvalOrder() int {
	trace := 0
	lo := min(minMaxMark(&trace, 1, 9), minMaxMark(&trace, 2, 4), minMaxMark(&trace, 3, 6))
	hi := max(minMaxMark(&trace, 4, 9), minMaxMark(&trace, 5, 4), minMaxMark(&trace, 6, 6))
	return trace*100 + lo*10 + hi
}

func minMaxMark(trace *int, tag int, value int) int {
	*trace = *trace*10 + tag
	return value
}

func builtinMinMaxDefinedInt() int {
	a := minMaxEdgeInt(7)
	b := minMaxEdgeInt(3)
	c := min(a, b)
	d := max(a, b)
	return int(c)*10 + int(d)
}

func builtinMinMaxDefinedString() int {
	a := minMaxEdgeString("go")
	b := minMaxEdgeString("lean")
	c := min(a, b)
	d := max(a, b)
	return len(c)*10 + len(d)
}

func builtinMinMaxUntypedFloatContext() int {
	var x float64 = min(3, 2.5)
	var y float64 = max(3, 2.5)
	return int(x*10)*100 + int(y*10)
}

func builtinMinMaxGenericInts[T ~int](a T, b T) int {
	return int(min(a, b))*10 + int(max(a, b))
}

func builtinMinMaxGenericIntsSubject() int {
	return builtinMinMaxGenericInts(minMaxEdgeInt(8), minMaxEdgeInt(5))
}

func builtinMinMaxGenericStrings[T ~string](a T, b T) int {
	return len(min(a, b))*10 + len(max(a, b))
}

func builtinMinMaxGenericStringsSubject() int {
	return builtinMinMaxGenericStrings(minMaxEdgeString("a"), minMaxEdgeString("bbb"))
}

func builtinMinMaxExpressions() int {
	x := 3
	y := 5
	return min(x+y, x*3)*100 + max(y-x, y+x)
}
