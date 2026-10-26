package sub

type A struct{ X, Y int }
type Ints []int

func MakeA(x int) A { return A{x, x + 1} }
