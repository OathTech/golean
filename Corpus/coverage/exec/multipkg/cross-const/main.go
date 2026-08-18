package main

// Multi-package guardrail (raft W1.1, 2026-08-18): cross-package
// CONSTANTS — an untyped package const, a typed one, and an iota chain.
// go/types folds constant values at the use site, so this pins that the
// qualified-identifier constant path lowers by VALUE (and, for the
// typed constant, at the right defined type for arithmetic).

import "limits"

func crossConst() int {
	total := limits.MaxRetries * 3
	total += int(limits.DefaultBudget)
	total += limits.StateFollower + limits.StateLeader
	return total
}

func main() {}
