package main

// BUG-005 probe (bug-fix arc slice 4, 2026-08-19): isolates the spec's
// FORCED removal clause from the delete-everything shape the existing
// delete-during-range red pins. spec#For_statements (range clause, maps):
// "If a map entry that has not yet been reached is removed during
// iteration, the corresponding iteration value will not be produced."
//
// Each iteration deletes only the OTHER key and keeps the current one, so
// under any conforming implementation the loop runs EXACTLY once (the
// remaining key is removed before being reached) and the produced key
// survives: n=1, len(m)=1 — go run: 11, 400/400 runs both orders
// (artifacts/probe/map005, scratch). The snapshot machine produces both
// snapshot entries and each iteration deletes the other, so it returns
// n=2, len(m)=0 — 20 under every choice stream.

func mapDeleteUnreachedDuringRange() int {
	m := map[int]int{1: 1, 2: 2}
	n := 0
	for k := range m {
		n++
		delete(m, 3-k)
	}
	return n*10 + len(m)
}

func main() {
	println(mapDeleteUnreachedDuringRange())
}
