package base

// Inits counts executions of Seed's initializer: exactly-once package
// initialization means it ends at 1 no matter how many import edges
// reach this package.
var Inits int

var Seed = seed()

func seed() int {
	Inits++
	return 10
}
