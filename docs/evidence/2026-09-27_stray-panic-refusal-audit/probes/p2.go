package main

type T struct{ v int }

func (t *T) inc() { t.v++ }
func (t T) get() int { return t.v }

func probe() int {
	arr := [3]T{{1}, {2}, {3}}
	var fs []func()
	for i := range arr {
		fs = append(fs, (&arr[i]).inc)
	}
	for _, f := range fs {
		f()
	}
	var ps []*int
	for i := 0; i < 3; i++ {
		ps = append(ps, &i)
	}
	g := arr[1].get
	arr[1].v = 100
	s := 0
	for _, p := range ps {
		s += *p
	}
	var cl []func() int
	for _, x := range []int{7, 8} {
		cl = append(cl, func() int { return x })
	}
	println(arr[0].v, arr[1].v, arr[2].v, s, g(), cl[0](), cl[1]())
	return arr[0].v + arr[1].v + arr[2].v + s + g() + cl[0]() + cl[1]()
}

func main() { println(probe()) }
