package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Assignability WITHOUT a conversion (spec#Assignability: identical underlying
// types, one side unnamed): unnamed slice/map/func/chan/array/pointer values into
// defined-type slots — store, parameter, return, literal element, struct field,
// map key, channel send, box — through normalizeValueForTyAt.

type MyInts []int
type MyMap map[string]int
type MyFn func(int) int
type MyChan chan int
type MyArr [2]int
type P *int
type Holder struct {
	S MyInts
	M MyMap
	F MyFn
	A MyArr
}

func kindOf(i any) int {
	switch i.(type) {
	case []int:
		return 1
	case MyInts:
		return 2
	case map[string]int:
		return 3
	case MyMap:
		return 4
	case func(int) int:
		return 5
	case MyFn:
		return 6
	case [2]int:
		return 7
	case MyArr:
		return 8
	case <-chan int:
		return 9
	case chan int:
		return 10
	case MyChan:
		return 11
	case *int:
		return 12
	case P:
		return 13
	}
	return 0
}

func takeInts(s MyInts) int { return len(s) }
func giveInts() MyInts      { return []int{1, 2, 3} }

func sliceAssignability() int {
	var s MyInts = []int{1, 2}
	s = []int{1, 2, 3, 4}
	ch := make(chan MyInts, 1)
	ch <- []int{5}
	got := <-ch
	h := Holder{S: []int{6, 7}}
	lits := []MyInts{[]int{8}, {9, 10}}
	var i any = s
	return kindOf(i)*1000000 + len(s)*100000 + takeInts([]int{1})*10000 + len(giveInts())*1000 + got[0]*100 + len(h.S)*10 + len(lits[1])
}

func mapAssignability() int {
	var m MyMap = map[string]int{"a": 1}
	m = map[string]int{"b": 2, "c": 3}
	h := Holder{M: map[string]int{"d": 4}}
	var i any = m
	return kindOf(i)*100 + len(m)*10 + h.M["d"]
}

func funcAssignability() int {
	var f MyFn = func(x int) int { return x + 1 }
	h := Holder{F: func(x int) int { return x * 2 }}
	var i any = f
	return kindOf(i)*100 + f(1)*10 + h.F(3)
}

func chanAssignability() int {
	ch := make(chan int, 1)
	var r <-chan int = ch
	var s chan<- int = ch
	var mc MyChan = ch
	s <- 4
	var i any = r
	var j any = mc
	return kindOf(i)*100 + kindOf(j)*10 + <-r
}

func arrayAssignability() int {
	var a MyArr = [2]int{1, 2}
	m := map[MyArr]int{[2]int{1, 2}: 5}
	h := Holder{A: [2]int{3, 4}}
	var i any = a
	return kindOf(i)*1000 + m[a]*100 + h.A[1]*10 + a[0]
}

func pointerAssignability() int {
	x := 3
	var p P = &x
	*p = 4
	var i any = p
	return kindOf(i)*10 + x
}

func main() {}
