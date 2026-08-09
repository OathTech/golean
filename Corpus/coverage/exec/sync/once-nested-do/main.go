package main

import "sync"

// Do calling itself on the same Once deadlocks (probe p08; sync/once.go:
// "if f causes Do to be called, it will deadlock") — the inner Do
// parks on the started-but-not-done cell held by its own goroutine.
func nestedDo() int {
	var o sync.Once
	o.Do(func() {
		o.Do(func() {})
	})
	return 0
}

func main() {
	nestedDo()
}
