package main

// An interface-valued SUBJECT RESULT: the one shape that exercises the
// observation channel's `{"tag":"interface","dynamic":…,"value":…}`
// rendering. Before 2026-07-31 no corpus case returned one, and none
// could have passed: the Go harness handed the result through an `any`
// parameter, which collapses the box, so `reflect` never saw
// Kind()==Interface and Go could not emit an `interface` tag at any
// nesting depth (pre-merge audit 2026-07-31, finding 2). The harness now
// observes through a POINTER, so `Ty.dynamicName`'s stated contract —
// `reflect.Type.Name()`, i.e. the UNQUALIFIED name — is actually
// checked against Go rather than asserted.

type observedCode int

type observedPoint struct {
	X int
	Y int
}

// A DEFINED type's name must render unqualified ("observedCode", not
// "main.observedCode").
func interfaceObservationDefined() any {
	return observedCode(7)
}

// A predeclared type's dynamic name is its own spelling.
func interfaceObservationInt() any {
	return 7
}

func interfaceObservationBool() any {
	return true
}

func interfaceObservationString() any {
	return "hi"
}

// A struct dynamic value: the interface wrapper AND the struct's own
// typeName field, both unqualified, in one object.
func interfaceObservationStruct() any {
	return observedPoint{X: 1, Y: 2}
}

// A NIL interface has no dynamic type at all.
func interfaceObservationNil() any {
	return nil
}

// A named interface (not `any`) as the static result type.
type observedStringer interface{ describe() int }

func (c observedCode) describe() int { return int(c) }

func interfaceObservationNamedIface() observedStringer {
	return observedCode(3)
}
