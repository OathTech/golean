// Thin main for the choice-driven twin driver (campaign Arc 1).
// Machine: artifacts/nativefrontend + golean native-json-run
// --function probeTwinChoice (one run per stream; the ∀-stream form
// is the T1 statement's, by proof — never by enumeration, which is
// intractable at this scale and is not the claim's mechanism).
// go run: each execution samples ONE delivery order (Go's own map
// nondeterminism) — a membership-style sample, not a strict twin.
package main

func main() { println(probeTwinChoice()) }
