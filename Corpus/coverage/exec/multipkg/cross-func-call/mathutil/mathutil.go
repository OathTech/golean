package mathutil

// Add is the minimal exported cross-package callee.
func Add(a, b int) int {
	return a + b
}

// Double calls a package-PRIVATE helper: the callee's own
// intra-package calls must keep resolving inside its package.
func Double(x int) int {
	return times(x, 2)
}

func times(a, b int) int {
	return a * b
}
