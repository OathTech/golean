package main

// S23 sweep (resource budgets; lane sweep/s23-budgets, 2026-11-05): the make
// door reached from a PACKAGE INITIALIZER with a run-time count — the frontend
// sees a call initializer and exports; the machine refuses by name during
// $pkginit (the message carries the `package init:` prefix and the make site's
// text, cause unsupported:make-footprint-budget-runtime). gc allocates the
// 32 MiB at init and answers 32768. RED BY DESIGN on BUG-131's Cases line;
// its own package because an init-time refusal reaches every subject.

func mk(n int) [][1024]byte { return make([][1024]byte, n) }

var big = mk(1 << 15)

func initMake() int { return len(big) }

func main() { println(initMake()) }
