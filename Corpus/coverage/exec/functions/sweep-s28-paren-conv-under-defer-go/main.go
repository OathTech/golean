// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). A conversion spelled with a
// parenthesised func type as the callee of defer and go — `defer (func())(f)()`,
// `go (func(int))(g)(1)` — and an explicit instantiation with a parenthesised type
// PARAMETER inside a generic body, `ident[(T)](x)`; expected = gc go1.26.5.

package main

type myF func()

func ident[T any](x T) T { return x }

func viaParenT[T ~int](x T) T { return ident[(T)](x) + ident[(T)](1) }

func parenConvUnderDeferGo() int {
	n := 0
	var f myF = func() { n += 1 }
	done := make(chan bool)
	g := func(k int) { n += k * 10; done <- true }
	func() {
		defer (func())(f)()
		n += 100
	}()
	go (func(int))(g)(1)
	<-done
	return n + int(viaParenT(5))*1000 // 111 + 6000
}

func main() { println("parenConvUnderDeferGo", parenConvUnderDeferGo()) }
