package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21: a library call shape gc rejects; the frontend must refuse it
// as a rejection (plan §4). Expected: gc rejects.

import "fmt"

func f() string { return fmt.Sprintf(1) }
func main() { f() }
