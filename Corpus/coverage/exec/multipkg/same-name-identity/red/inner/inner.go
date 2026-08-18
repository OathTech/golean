package inner

// The red T: same name, same shape as blue/inner.T and main.T —
// identical only to itself (identity is the import path).
type T struct {
	Tag int
}

func F() int {
	return 20
}
