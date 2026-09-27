package main

type S struct{ x, y int }

func f(n *int) int { *n++; return *n }

func probe() int {
	a := []int{10, 20, 30}
	i := 0
	i, a[i] = 1, 2
	a[i], i = i, a[i]
	x, y := 1, 2
	x, y = y, x
	m := map[int]int{}
	k := 0
	m[k] += f(&k)
	var s S
	s.x, s.y = s.y+1, s.x+2
	arr := [2]int{3, 4}
	arr[0], arr[1] = arr[1], arr[0]
	println(a[0], a[1], a[2], i, x, y, m[0], m[1], k, s.x, s.y, arr[0], arr[1])
	return a[0] + a[1] + a[2] + i + x + y + m[0] + m[1] + k + s.x + s.y + arr[0] + arr[1]
}

func main() { println(probe()) }
