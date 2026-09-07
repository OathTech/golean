package main

//go:noinline
func mk(a, b string) string { return a + b }

func main() {
	defer func() {
		_ = recover()
		panic(mk("or", "ig"))
	}()
	panic(mk("or", "ig"))
}
