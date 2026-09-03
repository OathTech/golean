// noodler frontier probe — field name at two depths: shallower wins
package main

type Deep struct{ X int }
type Mid struct {
	Deep
	Y int
}
type Top struct {
	Mid
	X int
}

// Field X exists at depth 0 and depth 2: the shallower wins; the deeper
// is reachable explicitly.
func fieldDepthConflictShallower() int {
	t := Top{Mid{Deep{1}, 2}, 3}
	t.X = 30
	t.Mid.X = 10
	return t.X + t.Mid.Deep.X + t.Y
}

func main() {}
