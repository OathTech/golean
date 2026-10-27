package main

type ints []int

func (s *ints) push(v int) { *s = append(*s, v) }

func main() {
	s := []int{1}
	ints(s).push(2) // a conversion's result is not addressable
}
