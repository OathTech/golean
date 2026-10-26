package main

func main() { run() }

type M map[int]int
type Sl []int
type Ch chan int
type Fn func()
type Empty struct{}
type A struct{ X, Y int }
type B struct{ X, Y int }

func run() {
	var m M
	var s Sl
	var c Ch
	var f Fn
	println(m == nil, s == nil, c == nil, f == nil, M(nil) == nil, Sl(nil) == nil, Ch(nil) == nil, Fn(nil) == nil)
	m = M{}
	s = Sl{}
	c = make(Ch)
	f = func() {}
	println(m != nil, s != nil, c != nil, f != nil, c == c, Ch(c) == c)
	println(Empty{} == struct{}{}, struct{}{} == Empty{}, any(Empty{}) == any(struct{}{}), any(Empty{}) == any(Empty{}), any(struct{}{}) == any(struct{}{}))
	var u uint64 = 1 << 63
	switch u {
	case 1 << 63:
		println("u matched 1<<63")
	case 1:
		println("u matched 1")
	}
	var i64 int64 = -1
	switch i64 {
	case -1:
		println("i64 -1")
	}
	m32 := map[float32]int{}
	f64 := 0.1
	m32[float32(f64)] = 1
	m32[0.1] = 2
	var f32 float32 = 0.1
	m32[f32] = 3
	println(len(m32), m32[0.1])
	m64 := map[float64]int{}
	m64[float64(f32)] = 1
	m64[0.1] = 2
	println(len(m64))
	a := A{1, 2}
	pb := (*B)(&a)
	println(*pb == B(a), *pb == B{1, 2}, *(*A)(pb) == a, A(*pb) == a)
	// equality of values read through the converted pointer after a write
	pb.X = 5
	println(a == A{5, 2}, *pb == B{5, 2})
	// compare array through pointer deref
	arr := [2]int{1, 2}
	pa := &arr
	println(*pa == [2]int{1, 2}, pa[0] == arr[0], &pa[1] == &arr[1])
	// comparing bytes via indexing of strings and slices
	str := "ab"
	bs := []byte(str)
	println(str[0] == bs[0], str[1] == 'b', bs[1] == str[1])
	// typed constant comparisons across kinds via conversions
	const big = 1 << 40
	println(int64(big) == big, uint64(big) == big, float64(big) == big)
	// rune/byte conversions and equality
	println(string(rune(65)) == "A", string(byte(65)) == "A", rune("A"[0]) == 'A')
	// pointer-to-pointer and interface of pointer to named map
	pm := &m
	println(pm == &m, *pm == nil)
}
