package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 (cells C2, C4): a DIAMOND — aa and bb both import cc — and
// main's own variable depending on an imported package's state. cc
// initializes once, before both importers (schedule 1 2 3); aa and bb
// both see cc.W as cc's init left it; main's initializer sees cc's
// variable and cc's init-set value.

import (
	"aa"
	"bb"
	"cc"
	"rec"
)

var mainV = cc.W*10 + cc.V

// diamondSeq is 123: cc, then aa, then bb (symbol order among the ready).
func diamondSeq() int { return rec.Seq }

// diamondOnce is 1: the shared dependency's init ran once.
func diamondOnce() int { return cc.Inits }

// importedInitSeen is 910: aa.V = 7 + 2, bb.V = 3 + 7.
func importedInitSeen() int { return aa.V*100 + bb.V }

// mainVar is 71: main's initializer reads cc.W (7) and cc.V (1).
func mainVar() int { return mainV }

func main() { println(diamondSeq(), diamondOnce(), importedInitSeen(), mainVar()) }
