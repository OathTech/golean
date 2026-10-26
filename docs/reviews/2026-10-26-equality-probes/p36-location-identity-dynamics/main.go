package main

func main() { run() }

func run() {
	s := make([]int, 1, 1)
	p := &s[0]
	s = append(s, 2)
	println("spill realloc:", p == &s[0])
	t := make([]int, 1, 2)
	q := &t[0]
	t = append(t, 2)
	println("in-cap append:", q == &t[0])
	var ps []*int
	for i := 0; i < 2; i++ {
		ps = append(ps, &i)
	}
	println("per-iteration loop var:", ps[0] == ps[1], *ps[0], *ps[1])
	var rs []*int
	for _, v := range []int{1, 2} {
		rs = append(rs, &v)
	}
	println("per-iteration range var:", rs[0] == rs[1], *rs[0], *rs[1])
	var ws []*int
	w := 0
	for w = 0; w < 2; w++ {
		ws = append(ws, &w)
	}
	println("shared outer var:", ws[0] == ws[1])
	var ns []*int
	for i := 0; i < 2; i++ {
		ns = append(ns, new(int))
	}
	println("new per iteration:", ns[0] == ns[1])
	var cs []*int
	for i := 0; i < 2; i++ {
		c := i
		cs = append(cs, &c)
	}
	println("block var per iteration:", cs[0] == cs[1])
	fs := []func() *int{}
	for i := 0; i < 2; i++ {
		fs = append(fs, func() *int { return &i })
	}
	println("closures over loop var:", fs[0]() == fs[1](), fs[0]() == ps[0])
	arr := [2]int{}
	sl := arr[:]
	sl2 := append(sl[:1], 5)
	println("append within cap aliases:", &sl2[0] == &arr[0], arr[1] == 5)
	cp := make([]int, 2)
	copy(cp, arr[:])
	println("copy makes distinct:", &cp[0] == &arr[0])
}
