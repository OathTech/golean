package main

// `go` during package initialization — legal Go (spec §Package
// initialization: "An init function may launch other goroutines"), but
// FAIL-CLOSED this slice (charter: `go` in $pkginit stays refused;
// the init phase runs on the sequential driver, whose spawn arm
// refuses). RED PIN: flips only when a later slice runs init on the
// pool.

var initReport = make(chan int, 1)

func init() {
	go func() {
		initReport <- 3
	}()
}

func spawnInInit() int {
	return <-initReport
}

func main() {
	spawnInInit()
}
