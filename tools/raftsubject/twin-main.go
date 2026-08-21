// The combined twin entry (all schedules in ONE machine run). The twin
// itself — machinery, checker, schedules, per-group probe functions —
// lives in twin-lib.go; run any main here with runprobe.py
// --lib twin-lib.go. The per-group mains (twin-single-main.go,
// twin-elect-main.go, twin-perturb-main.go, twin-ticks-main.go) run the
// same battery split four ways — machine runs of the whole battery are
// interpreter-minutes long, and a split run bounds each verdict and
// names the group a stop belongs to.
package main

// probeTwin is THE combined observation: one string carrying the
// single-node reproduction and every schedule's full trace, compared
// byte-for-byte across the oracles by runprobe.py.
func probeTwin() string {
	installLogger()
	return "single=" + itoa(probeTwinSingle()) + "\n" +
		probeTwinElect() + probeTwinPerturb() + probeTwinTicks()
}

func main() {
	println(probeTwin())
}
