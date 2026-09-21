package main

func rec(f func() int) (r int) {
	defer func() {
		if e := recover(); e != nil {
			println("panic:", e.(error).Error())
			r = -1
		}
	}()
	return f()
}

// nil map compound: the store panics in phase 2, after f
func nilMapCompound() int {
	var m map[int]int
	f := func() int { println("f"); m = nil; return 1 }
	m[1] += f()
	return 0
}

// nil pointer compound: the load's nil deref is unordered against mut
func nilPtrCompound() int {
	var p *int
	y := 5
	mut := func() int { println("mut"); p = &y; return 1 }
	*p += mut()
	return y
}

func main() {
	println(rec(nilMapCompound))
	println(rec(nilPtrCompound))
}
