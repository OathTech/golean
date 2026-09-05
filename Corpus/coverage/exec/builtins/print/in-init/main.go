package main

// DESIGNED RED (stdlib slice 3, FR-29 iii): a print during package
// initialization — the `$pkginit` phase runs on the sequential driver,
// which has no output event fold; `runInitConfig` refuses by name rather
// than dropping the bytes (BUGS.md BUG-093).
var seeded = 1

func init() {
	println("init prints", seeded)
}

func inInit() int {
	return seeded
}
