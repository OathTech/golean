package main

// The D-12/H-20 TRIPWIRE (W4.3 item 4 — the W4.2 owed row "the D-12
// refusal itself"; docs/raft-w42-log.md item 1's three-axis ledger
// entry). The raftsubject logger.go initializer shape VERBATIM:
//
//	var p = &T{F: log.New(os.Stderr, ...)}
//
// must refuse the WHOLE export, and the refusal stands on three
// INDEPENDENT axes of initializerEffectIsolated — the &-composite
// shape, log.New outside pureUnmodeledCallees (audit F1's charter: an
// unmodeled call is not effect-free, and log.New RETAINS a writer
// later writes land on), and os.Stderr failing isolatedType. A future
// widening of any TWO of the three that silently admitted the third
// would flip this row PASS — the visible regression H-20 must not
// cause by accident.

import (
	"log"
	"os"
)

type wrapT struct{ L *log.Logger }

var quarWriter = &wrapT{L: log.New(os.Stderr, "raft", log.LstdFlags)}

var quarWriterSibling = 4

func quarWriterRead() int { return quarWriterSibling }

func main() { println(quarWriterRead(), quarWriter != nil) }
