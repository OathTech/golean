// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised callees under
// defer and go, and parenthesised expression statements; expected = gc go1.26.5. BUG-287's
// fix lane probed these as one-cell packages without rows; rowed here.

package main

type rec struct{ n int }

func (r *rec) add(k int) { r.n += k }

func addTo(r *rec, k int) { r.n += k }

func deferParenCallees() int {
	r := &rec{}
	func() {
		defer (addTo)(r, 1)
		defer ((addTo))(r, 10)
		defer (r.add)(100)
		defer (func() { r.n += 1000 })()
		fv := addTo
		defer (fv)(r, 10000)
	}()
	return r.n // 11111
}

func addSend(r *rec, k int, done chan bool) { r.n += k; done <- true }

func goParenCalleesJoined() int {
	r := &rec{}
	done := make(chan bool)
	go (addSend)(r, 1, done)
	<-done
	go (func() { r.n += 10; done <- true })()
	<-done
	fv := func(k int) { r.n += k; done <- true }
	go (fv)(100)
	<-done
	go ((addSend))(r, 1000, done)
	<-done
	return r.n // 1111
}

func deferParenBuiltins() int {
	ch := make(chan int, 1)
	func() {
		defer (close)(ch)
		ch <- 4
	}()
	v, ok := <-ch
	_, ok2 := <-ch
	got := 0
	func() {
		defer (recover)()
		got = 1
	}()
	if ok && !ok2 {
		return v*10 + got // 41
	}
	return -1
}

func deferParenRecoverSwallows() int {
	got := 0
	func() {
		defer func() {
			if r := recover(); r != nil {
				got = 2
			}
		}()
		func() {
			defer (recover)() // a direct recover in defer position is a no-op: the panic propagates
			panic("boom")
		}()
		got = 1
	}()
	return got // 2
}

func count(n *int, k int) int { *n += k; return *n }

func parenExprStmts() int {
	n := 0
	(count(&n, 1))
	((count(&n, 10)))
	r := &rec{}
	(r.add(5))
	ch := make(chan int, 1)
	ch <- 1
	(<-ch)
	(func() { n += 100 }())
	return n*10 + r.n // 1115
}

func main() {
	println("deferParenCallees", deferParenCallees())
	println("goParenCalleesJoined", goParenCalleesJoined())
	println("deferParenBuiltins", deferParenBuiltins())
	println("deferParenRecoverSwallows", deferParenRecoverSwallows())
	println("parenExprStmts", parenExprStmts())
}
