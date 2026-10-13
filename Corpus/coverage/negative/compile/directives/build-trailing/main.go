package main

// BUG-127 fix round: a //go:build after code on its line (the reviewer's
// a8) — «misplaced compiler directive».
func main() { x := 1 //go:build foo
	println(x)
}
