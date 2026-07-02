package main

type copyEdgeBytes []byte
type copyEdgeInts []int

func builtinCopyEvalOrder() int {
	trace := 0
	dst := []int{0, 0, 0}
	src := []int{4, 5}
	n := copy(copyMarkIntSlice(&trace, 1, dst), copyMarkIntSlice(&trace, 2, src))
	return trace*100000 + n*10000 + dst[0]*1000 + dst[1]*100 + dst[2]
}

func copyMarkIntSlice(trace *int, tag int, xs []int) []int {
	*trace = *trace*10 + tag
	return xs
}

func builtinCopyDefinedSlices() int {
	dst := copyEdgeInts{0, 0, 0}
	src := copyEdgeInts{7, 8}
	n := copy(dst, src)
	return n*1000 + dst[0]*100 + dst[1]*10 + dst[2]
}

func builtinCopyDefinedByteString() int {
	dst := copyEdgeBytes{0, 0, 0, 0}
	n := copy(dst, "go")
	return n*10000 + int(dst[0])*100 + int(dst[1])
}

func builtinCopyEmptyStringToBytes() int {
	dst := []byte{1, 2}
	n := copy(dst, "")
	return n*100 + int(dst[0])*10 + int(dst[1])
}

func builtinCopyNilSource() int {
	var src []int
	dst := []int{1, 2}
	n := copy(dst, src)
	return n*100 + dst[0]*10 + dst[1]
}

func builtinCopyNilDestination() int {
	var dst []int
	src := []int{3, 4}
	n := copy(dst, src)
	return n*100 + len(dst)*10 + cap(dst)
}

func builtinCopyForwardOverlap() int {
	xs := []int{1, 2, 3, 4, 5}
	n := copy(xs[1:], xs[:4])
	return n*100000 + xs[0]*10000 + xs[1]*1000 + xs[2]*100 + xs[3]*10 + xs[4]
}

func builtinCopyArraySlice() int {
	dst := [4]int{}
	src := [3]int{5, 6, 7}
	n := copy(dst[:], src[:])
	return n*10000 + dst[0]*1000 + dst[1]*100 + dst[2]*10 + dst[3]
}

func builtinCopyStringPrefix() int {
	dst := []byte{0, 0}
	n := copy(dst, "abcd")
	return n*10000 + int(dst[0])*100 + int(dst[1])
}

func builtinCopyGeneric[T ~[]int](dst T, src T) int {
	n := copy(dst, src)
	return n*1000 + dst[0]*100 + dst[1]*10 + len(dst)
}

func builtinCopyGenericSubject() int {
	dst := copyEdgeInts{0, 0, 0}
	src := copyEdgeInts{2, 9, 8}
	return builtinCopyGeneric(dst, src)
}
