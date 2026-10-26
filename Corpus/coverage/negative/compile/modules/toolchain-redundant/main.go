package main

// Train-19 shake review F2 (2026-10-26; [USER] ruling of 2026-10-26, relayed:
// implement gc's condition for the `toolchain` line, plus the pin): the
// program is valid Go — the rejection is the go.mod beside it, whose
// `toolchain go1.26.5` is not above its `go 1.26.5` line. gc (go1.26.5,
// module mode, GOTOOLCHAIN=local, GOPROXY=off) drops such a line as
// redundant and under the default -mod=readonly refuses to build with the
// substring in case.tsv; the native frontend's module scanner
// (tools/nativefrontend/modfile.go judgeToolchain) refuses it by name as the
// `module` class. Before 2026-10-26 the frontend exported this directory: an
// admission false green (gc refuses, the frontend lowered).

func F() int { return 7 }

func main() { println(F()) }
