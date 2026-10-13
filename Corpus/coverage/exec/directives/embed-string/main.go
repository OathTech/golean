package main

import _ "embed"

// data.go is a sibling Go file: the oracle harness copies the package's
// *.go files only, so a data.txt would never reach the go-run
// directory, while data.go does and gc embeds its bytes.
//
//go:embed data.go
var src string

func embedNonEmpty() bool { return len(src) > 0 }

func main() { println(embedNonEmpty()) }
