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

// W4.3 item 5: a concrete R-1 forced-half control. The [recovered,
// repanicked] collapse depends on eface data identity. This Go == test
// checks VALUE equality; it does not expose or establish that runtime
// boxing identity. The abort row's explicit string-member certificate
// separately checks actual abort, full model chain and exact controls.
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
