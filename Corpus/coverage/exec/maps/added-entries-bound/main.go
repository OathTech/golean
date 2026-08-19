package main

// BUG-005 envelope-bound probe (bug-fix arc slice 4, 2026-08-19). The
// added-entries clause is GENUINE spec latitude — spec#For_statements
// (range clause, maps): "If a map entry is created during iteration, that
// entry may be produced during the iteration or may be skipped. The choice
// may vary for each entry created and from one iteration to the next."
//
// So no single iteration count can be pinned; what CAN be pinned is the
// envelope's bound: the original entry is produced exactly once, the one
// added entry at most once, so n ∈ {1, 2} and every produced key is a key
// the map ever held. gc exhibits BOTH members across plain re-runs
// (artifacts/probe/map005 probe A: a 4+4 shape realized every count from
// "no added entry produced" to "all produced" in 400 runs). The subject
// normalizes the member away and returns 7 iff the observation lies inside
// the envelope — green under the snapshot model (which resolves the
// latitude to "never produced"), green under any conforming live model,
// RED if a fix ever produces an added entry twice, produces a key the map
// never held, or fails to terminate.

func mapAddedEntriesBound() int {
	m := map[int]int{1: 10}
	n := 0
	seen1, seen2 := 0, 0
	for k := range m {
		n++
		if n > 5 {
			return -2 // runaway: outside the envelope
		}
		switch k {
		case 1:
			seen1++
			m[2] = 20 // created during iteration: may be produced or skipped
		case 2:
			seen2++
		default:
			return -3 // a key the map never held
		}
	}
	if seen1 == 1 && seen2 <= 1 && n == seen1+seen2 {
		return 7
	}
	return -1
}

func main() {
	println(mapAddedEntriesBound())
}
