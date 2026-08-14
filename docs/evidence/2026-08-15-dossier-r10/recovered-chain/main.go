// R10 probe: the [recovered] chain — recover() then re-panic with a
// NEW value from the deferred function; gc renders the first panic
// with [recovered] and the second beneath it.
package main

func main() {
	defer func() {
		r := recover()
		_ = r
		panic("second")
	}()
	panic("first")
}
