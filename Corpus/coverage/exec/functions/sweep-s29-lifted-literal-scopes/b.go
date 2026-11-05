package main

// The second file: its init runs after main.go's (lexical file order) and its
// package-level literal is a $pkginit lift of its own segment.

var pkgG = func() int { return 40 }

func init() {
	f := func() int { return 50 }
	initSum += f()
}
