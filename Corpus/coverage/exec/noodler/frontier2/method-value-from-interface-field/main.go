// noodler frontier probe — method value bound from an interface-typed struct field
package main

type Sizer interface{ Size() int }
type five struct{}

func (five) Size() int { return 5 }

type holder struct{ s Sizer }

// Method value taken from an interface-typed struct field, then the
// field is replaced: the bound value keeps the old dynamic value.
func methodValueFromInterfaceField() int {
	h := holder{five{}}
	f := h.s.Size
	h.s = nil
	return f()
}

func main() {}
