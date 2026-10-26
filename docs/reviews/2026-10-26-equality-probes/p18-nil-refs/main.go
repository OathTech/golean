package main

func main() { run() }

type F func()

func run() {
	var f func()
	var nf F
	println(f == nil, nf == nil, F(f) == nil, nf != nil)
	g := func() {}
	nf = g
	println(nf == nil, nf != nil, g != nil)
	var m map[int]int
	println(m == nil, len(m) == 0)
	m = map[int]int{}
	println(m == nil, m != nil)
	m = nil
	println(m == nil)
	var s []int
	println(s == nil)
	s = s[:0]
	println(s == nil)
	s = []int{}
	println(s == nil, s != nil, len(s) == 0)
	s = s[:0]
	println(s == nil)
	s = nil
	println(s == nil)
	t := []int(nil)
	println(t == nil, t[:0] == nil, append(t, 1) == nil, append(t, []int{}...) == nil, append([]int(nil)) == nil)
	var b []byte
	println(b == nil, []byte("") == nil, []byte(nil) == nil, string(b) == "")
	var fi any = f
	println(fi == nil, fi == any(nf))
	var ie any = g
	println(ie == nil)
	type S struct{ F func() }
	var ss S
	println(ss.F == nil)
	type Z struct{ M map[int]int }
	var z Z
	println(z.M == nil, Z{}.M == nil)
	arr := [2]func(){}
	println(arr[0] == nil, arr[1] == nil)
	sf := []func(){nil, g}
	println(sf[0] == nil, sf[1] == nil)
}
