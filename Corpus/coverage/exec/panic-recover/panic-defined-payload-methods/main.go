package main

// Go's `preprintpanics` rewrites a panic payload to `v.Error()` (error) or
// `v.String()` (fmt.Stringer) BEFORE `printpanicval` reaches
// `printanycustomtype`, so only a METHOD-LESS defined type renders as
// `main.T(v)` (pre-merge audit 2026-07-31, finding 3 — the unconditional
// `main.T(v)` arm was a fail-closed → wrong-answer regression). Rendering the
// rewritten form would mean CALLING a method at abort time, which the terminal
// rule cannot do, so the two method-bearing rows are pinned RED (fail closed).

type payloadCode int

func (c payloadCode) Error() string { return "boom" }

type payloadName int

func (n payloadName) String() string { return "strung" }

type payloadPlain int

func panicDefinedErrorPayload() int {
	panic(payloadCode(9))
}

func panicDefinedStringerPayload() int {
	panic(payloadName(3))
}

func panicDefinedPlainPayload() int {
	panic(payloadPlain(7))
}

// ---- W4.3 item 5: the §S3(b)/R-1 FORCED-HALF proof rows ----
//
// The 2026-08-20 R-1 ruling splits these rows' observable: the forced
// half (panic occurred, payload KIND and identity, control flow, exit
// status) stays compared EXACTLY; the abort-line TEXT is quotiented
// (the spec describes none of preprintpanics' rewriting — the envelope
// admits conforming renderings, ours recorded). The abort rows above
// stay RED: the machine has NO member yet (renderPanicHead refuses to
// call a method at abort time — the C4 impossibility), and producing
// one is semantic-core work outside this lane. These rows PROVE the
// forced half per payload class, in-language: the same payloads
// recovered and inspected — kind via type assertion, identity via the
// method results and the value round-trip. A mismatch here would mean
// the row was never a rendering row at all (the anti-laundering
// branch) — it would stay red as a real divergence.

func recoverDefinedErrorPayload() string {
	out := ""
	func() {
		defer func() {
			r := recover()
			if r == nil {
				out = "no-panic"
				return
			}
			e, isErr := r.(error)
			v, isCode := r.(payloadCode)
			if !isErr || !isCode || v != 9 {
				out = "wrong-kind"
				return
			}
			out = "kind=error text=" + e.Error() + " v=9"
		}()
		panic(payloadCode(9))
	}()
	return out
}

func recoverDefinedStringerPayload() string {
	out := ""
	func() {
		defer func() {
			r := recover()
			if r == nil {
				out = "no-panic"
				return
			}
			v, isName := r.(payloadName)
			if _, isErr := r.(error); isErr || !isName || v != 3 {
				out = "wrong-kind"
				return
			}
			out = "kind=stringer text=" + v.String() + " v=3"
		}()
		panic(payloadName(3))
	}()
	return out
}
