# gc probes for BUG-004 item 4 (go1.26.5 = /usr/local/go, GO111MODULE=off, GODEBUG=panicnil=0, GOTRACEBACK=none; go run main.go; 20 s timeout).
# [AGENT] design writer, lane docs/bug004-item4-design-0930, 2026-09-30. Scratch runs of this day, not gate inputs; sources verbatim, stderr = first 3 lines, exit = go run's 'exit status' line (124 = timeout).

## p01_error_vs_stringer
```go
type B int
func (B) Error() string  { return "from-Error" }
func (B) String() string { return "from-String" }
func main() { panic(B(1)) }
```
stderr:
  panic: from-Error
  exit status 2

## p02_error_panics_string
```go
type E int
func (E) Error() string { panic("inner-string") }
func main() { panic(E(1)) }
```
stderr:
  fatal error: panic while printing panic value: inner-string
  goroutine 1 gp=0x36c3fd6c81e0 m=0 mp=0x5268c0 [running]:
  runtime.throw({0x36c3fd6ea2a0?, 0x49428c?})
  exit status 2

## p03_error_panics_typed
```go
type E int
type Inner struct{ x int }
func (E) Error() string { panic(Inner{7}) }
func main() { panic(E(1)) }
```
stderr:
  fatal error: panic while printing panic value: type main.Inner
  goroutine 1 gp=0x2a94883ba1e0 m=0 mp=0x5268c0 [running]:
  runtime.throw({0x2a94883d01c0?, 0x494340?})
  exit status 2

## p04_nil_receiver_deref
```go
type E struct{ msg string }
func (e *E) Error() string { return e.msg }
func main() { var e *E; panic(e) }
```
stderr:
  fatal error: panic while printing panic value: type runtime.errorString
  [signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0x47a780]
  goroutine 1 gp=0x19473d3c01e0 m=0 mp=0x5268c0 [running]:
  exit status 2

## p05_nil_receiver_const
```go
type E struct{ msg string }
func (e *E) Error() string { return "const-text" }
func main() { var e *E; panic(e) }
```
stderr:
  panic: const-text
  exit status 2

## p06_value_recv_on_nil_ptr
```go
type V int
func (V) Error() string { return "v-text" }
func main() { var p *V; panic(p) }
```
stderr:
  fatal error: panic while printing panic value: type runtime.plainError
  goroutine 1 gp=0x1cf43800a1e0 m=0 mp=0x5268c0 [running]:
  runtime.throw({0x1cf438020200?, 0x494286?})
  exit status 2

## p07_ptr_recv_value_payload
```go
type Q int
func (*Q) Error() string { return "q" }
type P struct{ a int }
func (*P) Error() string { return "p" }
func main() {
	defer func() { panic(P{5}) }()
	panic(Q(3))
}
```
stderr:
  panic: main.Q(3)
  	panic: (main.P) 0x497da8
  exit status 2

## p08_post_defer_state
```go
var msg = "before"
type E int
func (E) Error() string { return msg }
func main() {
	defer func() { msg = "after" }()
	panic(E(1))
}
```
stderr:
  panic: after
  exit status 2

## p09_recovered_not_called
```go
type E struct{ s string }
func (e E) Error() string { println("CALLED:" + e.s); return e.s }
func main() {
	func() {
		defer func() { recover() }()
		panic(E{"recovered-one"})
	}()
	println("after-recover")
	panic(E{"unrecovered"})
}
```
stderr:
  after-recover
  CALLED:unrecovered
  panic: unrecovered
  exit status 2

## p10_chain_order
```go
type E struct{ s string }
func (e E) Error() string { println("CALLED:" + e.s); return e.s }
func main() {
	defer func() { recover(); panic(E{"second"}) }()
	panic(E{"first"})
}
```
stderr:
  CALLED:second
  CALLED:first
  panic: first [recovered]
  exit status 2

## p11b_repanic_reboxed_smallint
```go
type C int
func (c C) Error() string { println("CALLED"); return "boom" }
func main() {
	defer func() { r := recover(); panic(r.(C)) }()
	panic(C(9))
}
```
stderr:
  CALLED
  CALLED
  panic: boom [recovered]
  exit status 2

## p11_repanic_same_box
```go
type E struct{ s string }
func (e *E) Error() string { println("CALLED:" + e.s); return e.s }
func main() {
	defer func() { r := recover(); panic(r) }()
	panic(&E{"same"})
}
```
stderr:
  CALLED:same
  panic: same [recovered, repanicked]
  exit status 2

## p12_repanic_distinct_equal
```go
type E struct{ s string }
func (e E) Error() string { println("CALLED:" + e.s); return e.s }
func main() {
	defer func() { recover(); panic(E{"x"}) }()
	panic(E{"x"})
}
```
stderr:
  CALLED:x
  panic: x [recovered, repanicked]
  exit status 2

## p13_panic_nil
```go
func main() {
	defer func() { r := recover(); panic(r) }()
	panic(nil)
}
```
stderr:
  panic: panic called with nil argument [recovered, repanicked]
  exit status 2

## p14_blocking_error
```go
type C int
func (C) Error() string { <-make(chan int); return "never" }
func main() { panic(C(9)) }
```
stderr:
  fatal error: all goroutines are asleep - deadlock!
  exit status 2

## p15_spawn_in_error
```go
type C int
func (C) Error() string { ch := make(chan string); go func() { ch <- "from-goroutine" }(); return <-ch }
func main() { panic(C(9)) }
```
stderr:
  panic: from-goroutine
  exit status 2

## p16_os_exit
```go
import "os"
type C int
func (C) Error() string { os.Exit(3); return "x" }
func main() { panic(C(9)) }
```
stderr:
  exit status 3

## p17_recover_inside_error
```go
type C int
func (C) Error() string {
	defer func() { r := recover(); println("inner-recover-nil:", r == nil) }()
	return "text"
}
func main() { panic(C(9)) }
```
stderr:
  inner-recover-nil: true
  panic: text
  exit status 2

## p18_stringer_wrong_sig
```go
type T int
func (T) String() int { return 1 }
type U int
func (U) Error(x int) string { return "no" }
func main() {
	defer func() { panic(U(4)) }()
	panic(T(3))
}
```
stderr:
  panic: main.T(3)
  	panic: main.U(4)
  exit status 2

## p19_promoted_error
```go
type inner struct{}
func (inner) Error() string { return "promoted-text" }
type Outer struct{ inner; n int }
func main() { panic(Outer{n: 1}) }
```
stderr:
  panic: promoted-text
  exit status 2

## p20_multiline
```go
type C int
func (C) Error() string { return "line-one\nline-two" }
func main() { panic(C(1)) }
```
stderr:
  panic: line-one
  	line-two
  exit status 2

## p21_unrecovered_equal_pair
```go
type E struct{ s string }
func (e *E) Error() string { println("CALLED:" + e.s); return e.s }
func main() {
	e := &E{"same"}
	defer func() { panic(e) }()
	panic(e)
}
```
stderr:
  CALLED:same
  panic: same
  exit status 2

## p22_error_loops
```go
type C int
func (C) Error() string { for {} }
func main() { panic(C(1)) }
```
stderr: (none)
  (timeout 20 s: hangs)

## p23_runtime_error_payload
```go
func main() {
	defer func() { r := recover(); panic(r) }()
	var a []int
	_ = a[3]
}
```
stderr:
  panic: runtime error: index out of range [3] with length 0 [recovered, repanicked]
  exit status 2

## p24_two_goroutines_blocking_error
```go
type C int
var ch = make(chan int)
func (C) Error() string { return "got" }
func main() {
	go func() { for { <-ch } }()
	panic(C(1))
}
```
stderr:
  panic: got
  exit status 2
