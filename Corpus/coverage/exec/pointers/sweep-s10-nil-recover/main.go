package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the RECOVER route of
// the nil-dereference panic — a recovered store continues the function
// (the kind is recoverable, not fatal), and the recovered value's Error()
// text is gc's (the payload TYPE is S12's; the text is probed here because
// it is where S10 and S12 meet).

type nrBox struct{ f int }

func storeRecovered() int {
	var p *nrBox
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		p.f = 1
	}()
	return r + 1
}

func errorText() string {
	var p *int
	text := "none"
	func() {
		defer func() {
			if e, ok := recover().(error); ok {
				text = e.Error()
			}
		}()
		*p = 1
	}()
	return text
}

func main() {}
