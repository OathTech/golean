// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Built-ins whose operands are calls — BUG-164's site (the speculative path's isBuiltinCall
// guard) and the builtin emitters: len/cap of every operand kind, append (elements and a
// spread), delete, min/max, make (slice len/cap, chan cap), clear, close, panic, print,
// copy, a len/min followed by an ordered call (the hoist), nested builtins, the blank and
// var-declaration forms, in a closure and in a generic function.

package main

var cnt int

func f() int           { cnt++; return 2 }
func g() int           { cnt++; return 3 }
func h() int           { cnt++; return 1 }
func fs() []int        { cnt++; return []int{10, 20, 30} }
func fs2() []int       { cnt++; return []int{7, 8} }
func fstr() string     { cnt++; return "abcd" }
func fm() map[int]int  { cnt++; return map[int]int{1: 1, 2: 2} }
func fch() chan int    { cnt++; ch := make(chan int, 4); ch <- 1; return ch }
func farr() [5]int     { cnt++; return [5]int{} }
func fpa() *[6]int     { cnt++; return &[6]int{} }
func fb() []byte       { cnt++; return make([]byte, 3) }
func fc() complex128   { cnt++; return complex(3, 4) }
func fd() []int        { cnt++; return []int{0, 0, 0} }

var gm = map[int]int{1: 1, 2: 2, 3: 3}

func gmf() map[int]int { cnt++; return gm }

func lenOfCallSlice() int    { cnt = 0; n := len(fs()); return cnt*100 + n }
func lenOfCallString() int   { cnt = 0; n := len(fstr()); return cnt*100 + n }
func lenOfCallMap() int      { cnt = 0; n := len(fm()); return cnt*100 + n }
func lenOfCallChan() int     { cnt = 0; n := len(fch()); return cnt*100 + n }
func lenOfCallArray() int    { cnt = 0; n := len(farr()); return cnt*100 + n }
func lenOfCallPtrArray() int { cnt = 0; n := len(fpa()); return cnt*100 + n }
func capOfCallSlice() int    { cnt = 0; n := cap(fs()); return cnt*100 + n }
func capOfCallChan() int     { cnt = 0; n := cap(fch()); return cnt*100 + n }
func capOfCallArray() int    { cnt = 0; n := cap(farr()); return cnt*100 + n }

func appendCalls() int {
	cnt = 0
	s := append(fs(), f(), g())
	return cnt*100 + len(s)*10 + s[3] + s[4]
}

func appendSpreadCall() int {
	cnt = 0
	s := append(fs(), fs2()...)
	return cnt*100 + len(s)*10 + s[4]
}

func deleteCalls() int {
	cnt = 0
	gm[2] = 2
	delete(gmf(), f())
	return cnt*100 + len(gm)
}

func minCalls() int {
	cnt = 0
	x := min(f(), g(), h())
	return cnt*100 + x
}

func maxCalls() int {
	cnt = 0
	x := max(f(), g())
	return cnt*100 + x
}

func makeSliceLenCall() int {
	cnt = 0
	s := make([]int, f())
	return cnt*100 + len(s)
}

func makeSliceLenCapCalls() int {
	cnt = 0
	s := make([]int, f(), g())
	return cnt*100 + len(s)*10 + cap(s)
}

func makeChanCapCall() int {
	cnt = 0
	ch := make(chan int, g())
	return cnt*100 + cap(ch)
}

func clearSliceCall() int {
	cnt = 0
	s := []int{1, 2}
	fsl := func() []int { cnt++; return s }
	clear(fsl())
	return cnt*100 + s[0] + s[1]
}

func clearMapCall() int {
	cnt = 0
	gm[2] = 2
	clear(gmf())
	r := cnt*100 + len(gm)
	gm[1], gm[2], gm[3] = 1, 2, 3
	return r
}

func closeCall() int {
	cnt = 0
	ch := make(chan int)
	fc := func() chan int { cnt++; return ch }
	close(fc())
	_, ok := <-ch
	if ok {
		return -1
	}
	return cnt * 100
}

func panicOfCall() (r int) {
	cnt = 0
	defer func() {
		v := recover().(int)
		r = cnt*100 + v
	}()
	panic(f())
}

func printCalls() int {
	cnt = 0
	print(f(), g())
	println(h())
	return cnt * 100
}


func appendSliceExprCall() int {
	cnt = 0
	s := []int{10, 20, 30}
	s = append(s[:f()], g())
	return cnt*100 + len(s)*10 + s[2]
}

func copyStringSourceCall() int {
	cnt = 0
	n := copy(fb(), fstr())
	return cnt*100 + n
}

func lenCallThenCall() int {
	cnt = 0
	x := len(fs()) + g()
	return cnt*100 + x
}

func minCallsThenCall() int {
	cnt = 0
	x := min(f(), g()) + h()
	return cnt*100 + x
}

func lenOfAppendCalls() int {
	cnt = 0
	n := len(append(fs(), f()))
	return cnt*100 + n
}

func blankLen() int {
	cnt = 0
	_ = len(fs())
	return cnt * 100
}

func varDeclLen() int {
	cnt = 0
	var n = len(fs())
	var m int = cap(fs())
	return cnt*100 + n + m
}

func capOfMakeCalls() int {
	cnt = 0
	c := cap(make([]int, f(), g()))
	return cnt*100 + c
}

func copyCalls() int {
	cnt = 0
	n := copy(fd(), fs())
	return cnt*100 + n
}

func fsg[T any](v T) []T { cnt++; return []T{v, v} }

func lenGeneric[T any](v T) int {
	n := len(fsg(v))
	m := cap(fsg[T](v))
	s := make([]T, f())
	return n*100 + m*10 + len(s)
}

func closureLen() int {
	cnt = 0
	r := 0
	inner := func() {
		n := len(fs())
		s := make([]int, f())
		r = n*10 + len(s)
	}
	inner()
	return cnt*100 + r
}

func genericLen() int {
	cnt = 0
	r := lenGeneric(5) + lenGeneric("x")
	return cnt*1000 + r
}

func main() {
	lenOfCallSlice()
	lenOfCallString()
	lenOfCallMap()
	lenOfCallChan()
	lenOfCallArray()
	lenOfCallPtrArray()
	capOfCallSlice()
	capOfCallChan()
	capOfCallArray()
	appendCalls()
	appendSpreadCall()
	deleteCalls()
	minCalls()
	maxCalls()
	makeSliceLenCall()
	makeSliceLenCapCalls()
	makeChanCapCall()
	clearSliceCall()
	clearMapCall()
	closeCall()
	panicOfCall()
	printCalls()
	appendSliceExprCall()
	copyStringSourceCall()
	lenCallThenCall()
	minCallsThenCall()
	lenOfAppendCalls()
	blankLen()
	varDeclLen()
	capOfMakeCalls()
	copyCalls()
	closureLen()
	genericLen()
}
