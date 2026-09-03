// noodler frontier probe — pointer-receiver methods on a named slice type
package main

type Stack []int

func (s *Stack) Push(x int) { *s = append(*s, x) }
func (s *Stack) Pop() int {
	old := *s
	x := old[len(old)-1]
	*s = old[:len(old)-1]
	return x
}
func (s Stack) Len() int { return len(s) }

// Pointer-receiver methods on a slice type mutate the caller's header.
func stackSliceTypePointerMethods() (int, int, int) {
	var s Stack
	s.Push(1)
	s.Push(2)
	s.Push(3)
	x := s.Pop()
	return x, s.Len(), s[1]
}

func main() {}
