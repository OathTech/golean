package main

// AUDIT PROBES, set 2 (pre-merge audit of core/panic-preprint-1003,
// 2026-10-03; [AGENT] auditor): method-set corner cases gc's `error` /
// `stringer` checks hit — ambiguity, depth, embedded pointers, fields.

type ev struct{ s string }

func (e ev) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

type ea struct{}

func (ea) Error() string { return "a" }

type eb struct{}

func (eb) Error() string { return "b" }

// Q1 Error() promoted AMBIGUOUSLY (same depth twice): NOT in the method
// set -> gc prints the struct form `(main.ambig) 0x...`
type ambig struct {
	ea
	eb
}

func ambiguousPromoted() { panic(ambig{}) }

// Q2 the shallower promotion wins
type deep struct{ eb }

type shallow struct {
	ea
	deep
}

func shallowWins() { panic(shallow{}) }

// Q3 Error() ambiguous but String() unique: gc rewrites through String()
type sb struct{}

func (sb) String() string { return "s" }

type ambigS struct {
	ea
	eb
	sb
}

func ambiguousErrorUniqueStringer() { panic(ambigS{}) }

// Q4 a pointer-to-pointer payload has no methods
func ptrPtrPayload() {
	p := &ea{}
	panic(&p)
}

// Q5 a FIELD named Error of func type is not a method
type fieldErr struct{ Error func() string }

func fieldNotMethod() { panic(fieldErr{Error: func() string { return "x" }}) }

// Q6 promoted through a NON-nil embedded pointer; value receiver reads a field
type inner3 struct{ s string }

func (i inner3) Error() string { return i.s }

type outer3 struct{ *inner3 }

func embeddedPtrNonNil() { panic(outer3{&inner3{"z"}}) }

// Q7 String() promoted via an embedded (local) interface
type stringer interface{ String() string }

type sw struct{ stringer }

func stringerViaEmbeddedIface() { panic(sw{sb{}}) }

// Q8 a pointer-receiver Error() promoted into a VALUE's method set through
// an embedded pointer
type po struct{}

func (*po) Error() string { return "po" }

type embPtr struct{ *po }

func embeddedPtrPromotesPtrMethods() { panic(embPtr{&po{}}) }

// Q9 embedded by VALUE: the value lacks the pointer method, the pointer has it
type embVal struct{ po }

func embeddedValueLacksPtrMethod() { panic(embVal{}) }

func embeddedValuePtrHas() { panic(&embVal{}) }

// Q10 a direct String() beside a promoted Error(): Error still wins
type directS struct{ ea }

func (directS) String() string { return "direct-s" }

func directStringerPromotedError() { panic(directS{}) }

// Q17 two goroutines panic with error payloads concurrently
func twoGoroutinesPanicError() {
	go func() { panic(ev{"g"}) }()
	panic(ev{"m"})
}
