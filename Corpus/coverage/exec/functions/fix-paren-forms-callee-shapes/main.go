// Lane frontend/fix-paren-forms-1105 (2026-11-05): the parenthesised CALLEE
// at the two callee tests BUG-287's fix left — the selector dispatch and the
// immediately invoked literal. go/types evaluates call.Fun through its paren
// arm, so `(atomic.AddInt32)(&x, 2)` is the fused atomic op (before the fix:
// a by-name refusal of the "value position" selector), `(mu.Lock)()` and
// `defer (wg.Done)()` are the sync ops, `(strings.ToUpper)(s)` the shim,
// `(p.M)(x)` the method call, `(func(){…})()` the lifted literal's call,
// `(s.fn)(x)` the func-value call. Expected = gc go1.26.5.

package main

import (
	"strings"
	"sync"
	"sync/atomic"
)

type pt struct{ x, y int }

func (p pt) sum() int   { return p.x + p.y }
func (p *pt) bump() int { p.x++; return p.x }

type I interface{ sum() int }

type S struct{ fn func(int) int }

func dbl(a int) int { return a * 2 }

func parenCalleeAtomic() int32 {
	var x int32 = 5
	(atomic.AddInt32)(&x, 2)
	return (atomic.LoadInt32)(&x) // 7
}

func parenCalleeSync() int {
	var mu sync.Mutex
	var wg sync.WaitGroup
	n := 0
	(mu.Lock)()
	n = 1
	(mu.Unlock)()
	(wg.Add)(1)
	go func() {
		defer (wg.Done)()
		mu.Lock()
		defer (mu.Unlock)()
		n += 2
	}()
	(wg.Wait)()
	return n // 3
}

func parenCalleeShim() string { return (strings.ToUpper)("ab") + (strings.Repeat)("c", 2) } // ABcc

func parenCalleeMethod() int {
	r := pt{1, 2}
	var i I = pt{4, 5}
	p := &pt{7, 0}
	return (r.sum)()*1000 + (r.bump)()*100 + (i.sum)()*10 + (p.bump)() // 3000+200+90+8 = 3298
}

func parenCalleeFuncLit() int {
	k := 3
	(func() { k++ })()
	return (func(d int) int { return k + d })(10) + (func() int { return 7 })() // 14+7 = 21
}

func parenCalleeFieldFunc() int {
	s := S{fn: dbl}
	m := map[string]func(int) int{"k": dbl}
	fs := []func(int) int{dbl}
	return (s.fn)(3)*100 + (m["k"])(4)*10 + (fs[0])(5) // 600+80+10 = 690
}

func main() {
	println("parenCalleeAtomic", parenCalleeAtomic())
	println("parenCalleeSync", parenCalleeSync())
	println("parenCalleeShim", parenCalleeShim())
	println("parenCalleeMethod", parenCalleeMethod())
	println("parenCalleeFuncLit", parenCalleeFuncLit())
	println("parenCalleeFieldFunc", parenCalleeFieldFunc())
}
