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
// stays red awaiting the machine's quotient member; this row proves
// the forced half (panic, repanic, same-value identity, deferred-call
// order) exactly.
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
