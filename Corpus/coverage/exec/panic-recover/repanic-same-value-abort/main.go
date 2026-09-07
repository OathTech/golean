package main

func repanicSameValueAbort() {
	defer func() {
		panic(recover())
	}()
	panic("orig")
}

func main() {
	repanicSameValueAbort()
}

// W4.3 item 5: the R-1 forced-half proof row. The [recovered,
// repanicked] collapse is eface IDENTITY — undecidable at the
// machine's value level (the C4 impossibility) — but the IDENTITY
// itself is in-language: recover the repanic in an outer frame and
// compare with == against the original value. The abort row above
// was red until landing chunk L3 (2026-09-07) put the collapse on the
// tape (`ChoiceSite.repanicCollapse`, both members enumerated, gc's
// draw checked ∈ set — PASS/membership; the (c)→(a) move awaited [USER]
// ratification at the merge gate — RULED [USER] 2026-09-07 at merge train
// round 24, «Go ahead with the merge», relayed by the [AGENT] coordinator,
// the merge-ask naming the C4 (c)→(a) move among the four items ratified);
// this row proves the forced half
// (panic, repanic, same-value identity, deferred-call order) exactly,
// as it did before.
func repanicSameValueForcedHalf() string {
	orig := "orig"
	out := ""
	func() {
		defer func() {
			r := recover()
			same := "diff"
			if r == orig {
				same = "same"
			}
			out = "outer-recovered " + same
		}()
		defer func() {
			panic(recover())
		}()
		panic(orig)
	}()
	return out
}
