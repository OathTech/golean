package main

// BUG-127 fix round: a //go:build after the package clause carries gc's
// GoBuildPragma flag, which only the package clause consumes — «misplaced
// compiler directive» (the reviewer's a5s: the frontend exported it and
// the model answered 5 where gc rejects the file).

//go:build ignore

func main() { println(5) }
