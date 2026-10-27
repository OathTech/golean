package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// ASSIGNABILITY WITHOUT A CONVERSION between a defined type and its unnamed
// underlying type (spec#Assignability: identical underlying types, one of them
// unnamed): the value takes the SLOT's type, so a later box names the slot's
// type, not the source's — slice / map / chan / func in both directions by
// `var`, and the slice at an argument, a return and a literal element; a
// defined type whose underlying type is an interface (`interface{}`, `error`)
// as the slot.

type dSlice []int

type dMap map[string]int

type dChan chan int

type dFunc func() int

type dAny interface{}

type dErr error

type tErr struct{}

func (tErr) Error() string { return "tErr" }

func classifySlice(a any) int {
	switch a.(type) {
	case dSlice:
		return 1
	case []int:
		return 2
	}
	return 0
}

func classifyMap(a any) int {
	switch a.(type) {
	case dMap:
		return 1
	case map[string]int:
		return 2
	}
	return 0
}

func classifyChan(a any) int {
	switch a.(type) {
	case dChan:
		return 1
	case chan int:
		return 2
	}
	return 0
}

func classifyFunc(a any) int {
	switch a.(type) {
	case dFunc:
		return 1
	case func() int:
		return 2
	}
	return 0
}

func sliceBothWays() (int, int) {
	var u []int = dSlice{1}
	var s dSlice = []int{2}
	var a any = u
	var b any = s
	return classifySlice(a), classifySlice(b)
}

func mapBothWays() (int, int) {
	var u map[string]int = dMap{"a": 1}
	var s dMap = map[string]int{"b": 2}
	var a any = u
	var b any = s
	return classifyMap(a), classifyMap(b)
}

func chanBothWays() (int, int) {
	var u chan int = make(dChan, 1)
	var s dChan = make(chan int, 1)
	var a any = u
	var b any = s
	return classifyChan(a), classifyChan(b)
}

func funcBothWays() (int, int) {
	var u func() int = dFunc(func() int { return 1 })
	var s dFunc = func() int { return 2 }
	var a any = u
	var b any = s
	return classifyFunc(a), classifyFunc(b)
}

func definedIfaceAssign() (dAny, any) {
	var x dAny = 3
	var y any = x
	return x, y
}

func definedErrorIface() (int, bool) {
	var e dErr = tErr{}
	var a any = e
	r := 0
	switch a.(type) {
	case tErr:
		r += 1
	case error:
		r += 10
	}
	return r, a == e
}

func takeU(u []int) any { return u }

func takeD(d dSlice) any { return d }

func sliceAtArg() (int, int) {
	return classifySlice(takeU(dSlice{1})), classifySlice(takeD([]int{1}))
}

func retU() []int { return dSlice{1} }

func retD() dSlice { return []int{1} }

func sliceAtReturn() (int, int) {
	var a any = retU()
	var b any = retD()
	return classifySlice(a), classifySlice(b)
}

func sliceAtElem() (int, int) {
	xs := [][]int{dSlice{1}}
	ds := []dSlice{[]int{1}}
	var a any = xs[0]
	var b any = ds[0]
	return classifySlice(a), classifySlice(b)
}

func main() {
	sliceBothWays()
}
