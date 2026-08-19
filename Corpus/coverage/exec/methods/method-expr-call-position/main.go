// Method expressions in CALL position (spec#Method_expressions: "T.Mv
// yields a function equivalent to Mv but with an explicit receiver as its
// first argument" — and the spec's own five-equivalent-invocations block
// includes the direct call forms `T.Mv(t, 7)` and `(T).Mv(t, 7)`).
//
// Landed guardrails-first by the bug-fix arc's triage slice (slice 5,
// mini-slice A2). Before the fix, method expressions were supported in
// VALUE position (`f1 := mefT.Mv`, green since the methods campaign) but
// refused in CALL position: `emitMethodCall`'s selection dispatch fell
// past the MethodVal and FieldVal branches into `unsup("selector call %s
// is not a method value")`, quarantining the whole declaration.
//
// The five rows are the paths `emitSelector`'s MethodExpr arm itself
// distinguishes — concrete value receiver, concrete POINTER receiver,
// INTERFACE method expression (a dispatch anchor with no captures),
// PROMOTED (embedded) method expression (wrapper receiver form), and the
// argument evaluation order through the call — so a routing fix cannot
// green one path while silently mis-lowering another.
//
// Every expectation computed from `go run` BEFORE the fix
// (artifacts/probe/triage-methodexpr, scratch): 307, 16, 409, 2006,
// 120307 in the order declared.
package main

type mecT struct{ a int }

func (tv mecT) Mv(x int) int  { return tv.a*100 + x }
func (tp *mecT) Mp(x int) int { tp.a += x; return tp.a }

type mecI interface{ Mv(int) int }

type mecInner struct{ b int }

func (i mecInner) Emb(x int) int { return i.b*1000 + x }

type mecOuter struct{ mecInner }

// Concrete value receiver.
func mecValueCall() int { t := mecT{a: 3}; return mecT.Mv(t, 7) }

// Concrete POINTER receiver: the mutation must land in t, so the trailing
// `+ t.a` fails if the receiver is copied rather than addressed.
func mecPointerCall() int { t := mecT{a: 3}; return (*mecT).Mp(&t, 5) + t.a }

// INTERFACE method expression: the wire callee is the dispatch anchor and
// the receiver arrives as the first argument, not as a capture.
func mecIfaceCall() int { var i mecI = mecT{a: 4}; return mecI.Mv(i, 9) }

// PROMOTED method expression: the receiver form is the promotion
// wrapper's, and the embedded hop must be taken on the argument.
func mecPromotedCall() int { o := mecOuter{mecInner{b: 2}}; return mecOuter.Emb(o, 6) }

var mecTrace int

func mecMark(tag, v int) int           { mecTrace = mecTrace*10 + tag; return v }
func mecMarkRecv(tag int, t mecT) mecT { mecTrace = mecTrace*10 + tag; return t }

// spec#Order_of_evaluation: the receiver argument is just the first
// argument here, so the two marker calls run left to right (trace 12).
func mecCallOrder() int {
	mecTrace = 0
	t := mecT{a: 3}
	r := mecT.Mv(mecMarkRecv(1, t), mecMark(2, 7))
	return mecTrace*10000 + r
}
