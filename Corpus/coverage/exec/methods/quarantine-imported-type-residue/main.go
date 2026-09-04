// H-3 residue (2026-09-04, lane fr24): a body that is QUARANTINED (H-3
// stub) used to leave the imported named types it had mentioned in the
// D5 method-set table (`importedNamed`) — `reflect.Value` here, recorded
// by `v := reflect.ValueOf(...)` before the call refused. The D5 stub pass
// then needed EVERY signature of that type to lower, `Value.Complex()
// complex128` does not, and the WHOLE export refused — from a body that
// was already stubbed out, for a subject that never touches reflect. The
// registration now rides the mono journal and rolls back with the body
// (mono.go monoLogImportedNamed). `unrelated` is the green witness;
// `usesReflect` stays red BY NAME at frontend-export (the reflect surface
// is not modeled — FR-14's family), which is the H-3 contract.
package main

import "reflect"

func usesReflect() int {
	v := reflect.ValueOf([]int{1, 2, 3})
	return v.Len()
}

func unrelated() int { return 42 }

func main() { println(unrelated(), usesReflect()) }
