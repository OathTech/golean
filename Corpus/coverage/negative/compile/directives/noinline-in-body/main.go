package main

// BUG-127 fix round (review HIGH-1): gc rejects a //go:noinline that no
// func or method declaration consumes («misplaced compiler directive»);
// main's frontend exported this program and the model answered 1.
func main() {
	//go:noinline
	println(1)
}
