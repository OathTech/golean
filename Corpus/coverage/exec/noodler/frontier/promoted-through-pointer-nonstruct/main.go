// noodler frontier probe — method promoted through an embedded pointer to a non-struct defined type
package main

type Word string

func (w Word) Len() int { return len(w) }

type Holder struct {
	*Word
	n int
}

// Promotion through an embedded POINTER to a non-struct named type.
func promotedThroughPointerNonStruct() int {
	w := Word("four")
	h := Holder{&w, 1}
	return h.Len() + h.n
}

func main() {}
