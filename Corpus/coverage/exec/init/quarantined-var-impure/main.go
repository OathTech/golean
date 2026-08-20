package main

// H-11 boundary pin: a failing initializer whose LOWERABLE parts have
// potential effects on modeled state is NOT effect-isolated, so it
// keeps the whole-export refusal. Here the unmodeled os.Getenv carries
// a source-call ARGUMENT (bump() mutates a modeled global): skipping
// the initializer would lose bump's effect while go run performs it —
// a silent wrong answer for readers of impureCounter. The eligibility
// predicate refuses (a call inside the argument subtree), and the
// whole export stays red at frontend-export.

import "os"

var impureCounter int

func bump() string {
	impureCounter++
	return "GOLEAN_H11_IMPURE"
}

var impureMix = os.Getenv(bump())

func quarImpureCounter() int { return impureCounter }

func main() { println(quarImpureCounter()) }
