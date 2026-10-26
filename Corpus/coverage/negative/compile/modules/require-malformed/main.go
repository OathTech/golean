package main

// DC06 (deep-clean review 2026-10-26, FE-03/FE-04; [USER] ruling 2026-10-26,
// relayed): the program is valid Go — the rejection is the go.mod beside it.
// gc (go1.26.5, module mode, GOTOOLCHAIN=local, GOPROXY=off) refuses the
// module with the substring in case.tsv; the native frontend's module
// scanner (tools/nativefrontend/modfile.go) refuses it by name as the
// `module` class. Before 2026-10-26 the frontend exported this directory.

func F() int { return 7 }

func main() { println(F()) }
