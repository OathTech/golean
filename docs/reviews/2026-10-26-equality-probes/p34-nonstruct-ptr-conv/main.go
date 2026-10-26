package main

func main() { run() }

type MyInt int
type Arr [2]int
type MyStr string
type MyF float64
type MyB bool
type Fn func()
type MyChan chan int
type Sl []int

func run() {
	x := 5
	p := (*MyInt)(&x)
	println(*p == 5, *p == MyInt(x), (*int)(p) == &x)
	*p = 7
	println(x == 7, *p == 7)
	arr := [2]int{1, 2}
	pa := (*Arr)(&arr)
	println(*pa == Arr{1, 2}, arr == [2]int(*pa), &pa[1] == &arr[1])
	pa[0] = 9
	println(arr == [2]int{9, 2}, *pa == Arr{9, 2})
	s := "a"
	ps := (*MyStr)(&s)
	println(*ps == "a", *ps < "b")
	*ps = "z"
	println(s == "z")
	f := 1.5
	pf := (*MyF)(&f)
	println(*pf == 1.5, *pf > 1)
	b := true
	pb := (*MyB)(&b)
	println(*pb == true, *pb)
	var fn func()
	pfn := (*Fn)(&fn)
	println(*pfn == nil)
	ch := make(chan int)
	pc := (*MyChan)(&ch)
	println(*pc == ch, ch == chan int(*pc), *pc != nil)
	sl := []int{1}
	psl := (*Sl)(&sl)
	println(*psl != nil, len(*psl) == 1, &(*psl)[0] == &sl[0])
	var u uintptr = 7
	println(u == 7, u+1 == 8, uintptr(1)<<63 > 0)
	switch r := 'é'; r {
	case 'e':
		println("e")
	case 'é':
		println("e-acute")
	}
}
