package main

// A main package with no func main: gc rejects the PROGRAM ("function main
// is undeclared in the main package"). The native frontend refuses it too
// by default (a type-check-class rejection; tools/nativefrontend/
// entrymode.go). Born FAIL at frontend-accepts 2026-10-12, PASS since the
// 2026-10-13 fix — docs/BUGS.md BUG-125.
func f() int { return 1 }
