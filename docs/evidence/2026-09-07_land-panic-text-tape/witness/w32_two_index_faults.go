package main

//go:noinline
func idx(s []int, i int) int { return s[i] }

func main() {
	s := []int{1}
	defer func() {
		_ = recover()
		_ = idx(s, 5)
	}()
	_ = idx(s, 5)
}
