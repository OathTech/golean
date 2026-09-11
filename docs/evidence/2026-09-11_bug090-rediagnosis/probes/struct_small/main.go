package main

// w scalar-field writes into a two-int struct (control for struct_arr_*).
type S struct {
	y int
	x int
}

func probe(w int) int {
	var s S
	for i := 0; i < w; i++ {
		s.x = i
	}
	return s.x + s.y
}
func main() {}
