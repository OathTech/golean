package main

// Excluded on linux/amd64 by the _windows suffix; would redeclare both
// names if it were part of the package.
var conflict = 99

func helper() int { return -1 }
