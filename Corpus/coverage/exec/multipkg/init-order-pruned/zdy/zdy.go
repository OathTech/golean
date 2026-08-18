package zdy

// DYNAMICALLY initialized: the assignment happens in a real `init`
// function, which staticinit cannot fold away, so zdy emits an
// `..inittask` and IS a node of gc's schedule. `dm`, which imports it,
// must wait for zdy.

var Y int

func init() { Y = 5 }
