package main

// F1 guardrail, second shape (audit fix round, raft W4.0 2026-08-20):
// an unmodeled callee whose effect is on the WORLD rather than on
// stdout. os.Mkdir is not on the pure-callee allowlist, so the
// initializer is not effect-isolated and the whole export refuses.
//
// The empty path is chosen deliberately: os.Mkdir("") always fails
// (ENOENT) on every platform, so the case creates nothing, is
// deterministic, and still carries the syscall SHAPE that must not be
// admitted. The sibling subject touches neither the error value nor
// anything else, so a re-opened allowlist would quarantine the var,
// export cleanly, and flip this row PASS — the visible regression.

import "os"

var quarMkdirErr = os.Mkdir("", 0o755)

var quarMkdirGood = 9

func quarMkdirSibling() int { return quarMkdirGood }

func main() { println(quarMkdirSibling(), quarMkdirErr != nil) }
