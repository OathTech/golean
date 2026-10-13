package main

import _ "unsafe"

// BUG-127: gc's linker rejects a pull linkname into a runtime symbol
// that is not push-linknamed («invalid reference to runtime.zerobase»);
// the frontend exported it and the model answered 0 before the
// directive refusal.
//
//go:linkname x runtime.zerobase
var x uintptr

func main() { println(x) }
