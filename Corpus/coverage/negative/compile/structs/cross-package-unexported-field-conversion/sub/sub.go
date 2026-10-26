package sub

// Unexported field names: identical spelling in two packages is NOT identity
// (spec#Type_identity). A and B here (one package) are convertible; main.C
// below, spelled the same, is not.
type A struct {
	x int
	Y int
}
type B struct {
	x int
	Y int
}

func (b B) Sum() int { return b.x + b.Y }

func MkA() *A       { return &A{1, 2} }
func Conv(p *A) *B  { return (*B)(p) }
func Peek(p *A) int { return p.x }
