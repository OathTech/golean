package main

import "fmt"

var w int

func wit(x int) int { w = w*31 + x; return x }

func assertLeftCall() (r int) {
	defer func() { recover(); r = w }()
	var iv interface{} = "s"
	return iv.(int) + wit(5)
}

func indexLeftCall() (r int) {
	defer func() { recover(); r = w }()
	s := []int{1}
	i := 9
	return s[i] + wit(5)
}

func callArgSibling() (r int) {
	defer func() { recover(); r = w }()
	var iv interface{} = "s"
	return sink(iv.(int), wit(7))
}

func sink(a, b int) int { return a + b }

func forcedArg() (r int) {
	defer func() { recover(); r = w }()
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + wit(t[k])
}

func targetIndex() int {
	a := []int{1, 2}
	i := 5
	a[i] = wit(3)
	return a[0]
}

func twoProbes() (r int) {
	defer func() { recover(); r = w }()
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + t[k] + wit(5)
}

func scRhs(x int) (r int) {
	defer func() { recover(); r = w }()
	a := []int{1}
	i := 9
	if x > 0 && a[i]+wit(5) > 0 {
		return 1
	}
	return 0
}

func loopCond() (r int) {
	defer func() { recover(); r = w }()
	a := []int{1, 2, 3}
	n := 0
	for i := 0; a[i] < wit(9); i++ {
		n++
	}
	return n
}

func recoverOperand() (r int) {
	defer func() {
		v := recover().(string) + fmt.Sprint(wit(1))
		r = len(v)
	}()
	panic("boom")
}

func main() {
	fmt.Println(assertLeftCall(), indexLeftCall(), callArgSibling(), forcedArg(), targetIndex(), twoProbes(), scRhs(1), loopCond(), recoverOperand())
}
