package note

// The foreign package of multipkg/sweep-s22-readout-crosspkg: a struct, a generic struct, two defined kinds.

type T struct{ V int }
type Kind int
type Name string
type Pair[A any] struct {
	A A
	B string
}
