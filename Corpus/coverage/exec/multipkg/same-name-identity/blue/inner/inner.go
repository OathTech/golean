package inner

// The blue T: structurally identical to red/inner.T, distinct type.
type T struct {
	Tag int
}

func F() int {
	return 300
}
