// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). BUG-027's closer
// `<fn>$deferClose<N>` and the sync closers at every scope the name is keyed by: two in
// one function, a method and a function of one name, two methods of one name, a func
// literal and its enclosing function, a generic function at two instantiations, two init
// functions, a loop, the parenthesised and element operands, `defer mu.Unlock()`,
// `once.Do` and `defer wg.Done()` in the same scopes; expected = gc go1.26.5.

package main

import "sync"

type tA struct{}
type tB struct{}

func (tA) run(ch chan int) { defer close(ch); ch <- 1 }
func (tB) run(ch chan int) { defer close(ch); ch <- 2 }

func run(ch chan int) { defer close(ch); ch <- 3 }

var initCh1 = make(chan int, 1)
var initCh2 = make(chan int, 1)

func init() {
	defer close(initCh1)
	initCh1 <- 7
}

func init() {
	defer close(initCh2)
	initCh2 <- 8
}

func drain(ch chan int) int {
	n := 0
	for v := range ch {
		n += v
	}
	return n
}

func twoClosersOneFunction() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	func() {
		defer close(a)
		defer close(b)
		a <- 1
		b <- 2
	}()
	return drain(a)*10 + drain(b) // 12
}

func closersSameNameMethodsAndFunc() int {
	a, b, c := make(chan int, 1), make(chan int, 1), make(chan int, 1)
	tA{}.run(a)
	tB{}.run(b)
	run(c)
	return drain(a)*100 + drain(b)*10 + drain(c) // 123
}

func closerInLiteralAndEnclosing() int {
	outer := make(chan int, 1)
	inner := make(chan int, 1)
	func() {
		defer close(outer)
		func() {
			defer close(inner)
			inner <- 4
		}()
		outer <- 5
	}()
	return drain(outer)*10 + drain(inner) // 54
}

func gClose[T any](v T, ch chan T) { defer close(ch); ch <- v }

func closerInGenericTwoInsts() int {
	a := make(chan int, 1)
	b := make(chan string, 1)
	gClose(6, a)
	gClose("ab", b)
	n := drain(a) * 10
	for s := range b {
		n += len(s)
	}
	return n // 62
}

func closersInInits() int {
	return drain(initCh1)*10 + drain(initCh2) // 78
}

func closerInLoop() int {
	chs := []chan int{make(chan int, 1), make(chan int, 1), make(chan int, 1)}
	func() {
		for i := range chs {
			defer close(chs[i])
			chs[i] <- i + 1
		}
	}()
	return drain(chs[0])*100 + drain(chs[1])*10 + drain(chs[2]) // 123
}

func getCh(chs []chan int, i int) chan int { return chs[i] }

func closerOperandSpellings() int {
	chs := []chan int{make(chan int, 1), make(chan int, 1)}
	ch := make(chan int, 1)
	func() {
		defer close((ch))
		defer close(chs[1])
		defer close(getCh(chs, 0))
		ch <- 1
		chs[0] <- 2
		chs[1] <- 3
	}()
	return drain(ch)*100 + drain(chs[0])*10 + drain(chs[1]) // 123
}

type locked struct {
	mu sync.Mutex
	n  int
}

func (l *locked) add(k int) { l.mu.Lock(); defer l.mu.Unlock(); l.n += k }

func addTwice(l *locked) {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.n++
	func() {
		m := &locked{}
		m.mu.Lock()
		defer m.mu.Unlock()
		m.n++
		l.n += m.n
	}()
}

func gLock[T ~int](l *locked, v T) {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.n += int(v)
}

type myI int

func deferUnlockScopes() int {
	l := &locked{}
	l.add(1)
	addTwice(l)
	gLock(l, 10)
	gLock(l, myI(100))
	func() {
		l.mu.Lock()
		defer l.mu.Unlock()
		l.n += 1000
		l.mu.Unlock()
		l.mu.Lock()
	}()
	l.mu.Lock()
	l.n += 10000
	l.mu.Unlock()
	return l.n // 11113
}

var onceA, onceB sync.Once
var onceN int

func onceUser1() { onceA.Do(func() { onceN += 1 }); onceA.Do(func() { onceN += 100 }) }
func onceUser2() { onceB.Do(func() { onceN += 10 }) }

func gOnce[T ~int](o *sync.Once, v T) { o.Do(func() { onceN += int(v) }) }

func onceDoScopes() int {
	onceN = 0
	onceUser1()
	onceUser2()
	func() {
		var o sync.Once
		o.Do(func() { onceN += 1000 })
	}()
	var o1, o2 sync.Once
	gOnce(&o1, 10000)
	gOnce(&o2, myI(100000))
	return onceN // 111011
}

func deferDoneTwoLiterals() int {
	var wg sync.WaitGroup
	var mu sync.Mutex
	n := 0
	wg.Add(2)
	go func() { defer wg.Done(); mu.Lock(); n += 1; mu.Unlock() }()
	go func() { defer wg.Done(); mu.Lock(); n += 10; mu.Unlock() }()
	wg.Wait()
	return n // 11
}

func main() {
	println("twoClosersOneFunction", twoClosersOneFunction())
	println("closersSameNameMethodsAndFunc", closersSameNameMethodsAndFunc())
	println("closerInLiteralAndEnclosing", closerInLiteralAndEnclosing())
	println("closerInGenericTwoInsts", closerInGenericTwoInsts())
	println("closersInInits", closersInInits())
	println("closerInLoop", closerInLoop())
	println("closerOperandSpellings", closerOperandSpellings())
	println("deferUnlockScopes", deferUnlockScopes())
	println("onceDoScopes", onceDoScopes())
	println("deferDoneTwoLiterals", deferDoneTwoLiterals())
}
