package main

import _ "unsafe"

// A linkname gc ACCEPTS: the directive only renames seven's object
// symbol (no pull into another package), so `go build` links and prints
// 7. Refused all the same: no directive outside the allowlist is modeled.
//
//go:linkname seven example.org/x.seven
func seven() int { return 7 }

func linknamedCall() int { return seven() }

func main() { println(linknamedCall()) }
