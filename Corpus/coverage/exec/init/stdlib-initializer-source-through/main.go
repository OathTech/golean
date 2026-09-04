package main

import (
	"errors"
	"strings"
)

// Source-through callee in a package-level initializer: routed through the
// library loader, so the var is REAL (not poisoned) and readable.
var banner = strings.Repeat("ab", 3)
var sentinel = errors.New("boom")

func readBanner() string { return banner + ":" + sentinel.Error() }

func main() { println(readBanner()) }
