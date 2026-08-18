package main

// spec#Type_inference block Type_inference-1-21633371: type inference makes
// s = dedup(s) with s of named type Slice equivalent to
// s = dedup[Slice, int](s) — S is inferred as Slice (satisfying ~[]E), E as
// int, and the RESULT type is Slice again (assignable back to s with no
// conversion). The spec's elided dedup body is realized as
// keep-first-occurrence.

// dedup returns a copy of the argument slice with any duplicate entries removed.
func dedup[S ~[]E, E comparable](s S) S {
	var out S
	seen := map[E]bool{}
	for _, x := range s {
		if !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	return out
}

type Slice []int

func dedupInference() int {
	var s Slice = Slice{1, 2, 1, 3, 2}
	s = dedup(s) // same as s = dedup[Slice, int](s)
	n := 0
	for _, v := range s {
		n = n*10 + v
	}
	return n // 123
}
