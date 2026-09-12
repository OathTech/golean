package main

// Included everywhere: a bare OS name with no underscore prefix is not a
// build tag (go/build goodOSArchFile, the Go 1.4 rule).
func init() { fromBareLinux = 2 }
