package main

// Train-20 pre-merge audit F4 (2026-10-26; [USER] ruling relayed: fix as the
// same class as the shake review's F2 — a go.mod gc refuses that the scanner
// exported, pre-existing on main): the program is valid Go — the rejection is
// the go.mod beside it. gc (go1.26.5, module mode, GOTOOLCHAIN=local,
// GOPROXY=off, GOWORK=off) refuses the module with the substring in case.tsv;
// the native frontend's module scanner (tools/nativefrontend/modfile.go, the
// header's paragraph (4): gc's lexer characters, major-version agreement,
// +incompatible as the only build metadata) refuses it by name as the
// `module` class. Before 2026-10-26 the frontend exported this directory.

func F() int { return 7 }

func main() { println(F()) }
