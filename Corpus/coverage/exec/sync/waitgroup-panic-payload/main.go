package main

import "sync"

// ARC-END fix-round pin (2026-08-10): the negative-counter panic's
// PAYLOAD CLASS. gc's sync package raises it with
// `panic("sync: negative WaitGroup counter")` (waitgroup.go:118) — a
// plain `string` value, package code, NOT a runtime `plainError` like
// the channel panics (runtime/chan.go). A recover that type-asserts
// the payload therefore sees a string: gc returns
// 1000+len("sync: negative WaitGroup counter") = 1032. The model
// carried `$runtime.Error` here — `.(string)` answered false, silently,
// with status ok (the abort TEXT is identical for both payload kinds,
// so the message-only pins in waitgroup-negative-panic cannot see it).
// Red-first before the payload-class fix.
func payloadIsString() int {
	r := 0
	func() {
		defer func() {
			if v := recover(); v != nil {
				if s, ok := v.(string); ok {
					r = 1000 + len(s)
				} else {
					r = 3
				}
			}
		}()
		var wg sync.WaitGroup
		wg.Add(1)
		wg.Done()
		wg.Done()
	}()
	return r
}

func main() {
	payloadIsString()
}
