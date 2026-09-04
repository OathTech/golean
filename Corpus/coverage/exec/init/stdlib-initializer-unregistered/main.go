package main

import "os"

// An unmodeled callee NOT on the init-callee register: the whole export
// still refuses (the sound direction), naming the var, the callee and the
// register.
var pid = os.Getpid()

func unrelated() int { return 7 }

func main() { println(unrelated()) }
