// noodler frontier probe — pointer-receiver method value through a nil embedded pointer (no deref)
package main

type In struct{ n int }

func (i *In) Zero() int { return 0 }

type Out struct{ *In }

// A pointer-receiver method value taken through a NIL embedded pointer:
// the method value is created and callable (the receiver is the nil
// pointer itself, never dereferenced).
func methodValueEmbeddedPointerNilOK() int {
	var o Out
	f := o.Zero
	return f() + 1
}

func main() {}
