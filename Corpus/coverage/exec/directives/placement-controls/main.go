package main

// The placements gc ACCEPTS for the allowlisted directives (BUG-127 fix
// round, review HIGH-1): a //go:noinline on a method, a //go:noinline
// separated from its func by a blank line, a //go:generate inside a body
// (it carries no pragma flag, so it is never misplaced on its own line).

type T int

//go:noinline
func (t T) M() int { return int(t) }

func noinlineMethod() int { return T(2).M() }

//go:noinline

func blankThenFunc() int { return 1 }

func noinlineBlankLine() int { return blankThenFunc() }

func generateInBody() int {
	//go:generate echo hi
	return 3
}

func main() { println(noinlineMethod(), noinlineBlankLine(), generateInBody()) }
