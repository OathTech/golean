## a_append_spill_oldptr
```go
package main

func probe() int {
	s := make([]int, 2, 2)
	p := &s[1]
	s = append(s, 5) // spill: new backing
	*p = 42          // old backing
	return s[1]*1000 + len(s)*10 + cap(s)/cap(s)
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_arrptr_redirect
```go
package main

func probe() int {
	a := [4]int{1, 2, 3, 4}
	b := [4]int{}
	pa := &a
	q := &pa[3]
	pa = &b
	*q = 99
	return a[3]*10 + b[3]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_clear_then_write
```go
package main

func probe() int {
	s := []int{1, 2, 3}
	p := &s[1]
	clear(s)
	*p = 4
	return s[1]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_closure_elem_spill
```go
package main

func probe() int {
	s := []int{1, 2, 3}
	p := &s[2]
	w := func(v int) { *p = v }
	for i := 0; i < 10; i++ {
		s = append(s, i)
	}
	w(77)
	return s[2]*10 + len(s)
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_copy_shorter
```go
package main

func probe() int {
	src := []int{1, 2, 3, 4, 5}
	dst := make([]int, 2)
	n := copy(dst, src)
	return n*100 + dst[0]*10 + dst[1]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_defer_elemptr
```go
package main

func setLater(p *int) func() { return func() { *p = 5 } }

func probe() int {
	a := [2]int{}
	f := setLater(&a[1])
	a = [2]int{1, 1}
	f()
	return a[1]*10 + a[0]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_nested_inner_replace
```go
package main

func probe() int {
	g := [][]int{{1, 2, 3}, {4, 5, 6}}
	p := &g[1][2]
	g[1] = make([]int, 1)
	*p = 9
	return g[1][0]*10 + len(g[1])
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_oob_store_target
```go
package main

func probe() int {
	a := [3]int{}
	s := a[:]
	i := 3
	s[i] = 1
	return a[0]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_ptr_reassign
```go
package main

func probe() int {
	a := [3]int{1, 2, 3}
	p := &a[2]
	a = [3]int{7, 8, 9}
	*p = 100
	return a[2]*1000 + a[0]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_reslice_shorter
```go
package main

func probe() int {
	s := make([]int, 5)
	p := &s[4]
	s = s[:2]
	*p = 7
	t := s[:5]
	return t[4]*10 + len(s)
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_slice_to_arrptr
```go
package main

func probe() int {
	s := []int{1, 2, 3, 4}
	t := s[1:]
	p := (*[2]int)(t)
	p[1] = 9
	return s[2]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_slice_to_arr_short
```go
package main

func probe() int {
	s := []int{1}
	a := [2]int(s)
	return a[0]
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_struct_arr_replace
```go
package main

type S struct{ a [3]int; x int }

func probe() int {
	var s S
	p := &s.a[2]
	s = S{a: [3]int{4, 5, 6}, x: 1}
	*p = 8
	return s.a[2]*10 + s.x
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_three_index_inplace
```go
package main

func probe() int {
	a := [6]int{}
	s := a[1:2:4]
	s = append(s, 7, 8)
	p := &s[2]
	s = append(s, 1) // spill
	*p = 5
	return a[3]*10 + len(s)
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## a_unseq_realloc
```go
package main

var s = make([]int, 3, 3)

func grow() int {
	s = append(s, 9) // spill during the statement
	return 1
}

func probe() int {
	i := 2
	s[i], i = grow(), 0
	return s[2]*10 + len(s)
}
func main() { defer func() { if r := recover(); r != nil { println("panic:", r.(error).Error()) } }(); println(probe()) }
```

## b_allocnew_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var pp **int

func probe() int { *pp = new(int); return 1 }
func main() { show(probe) }
```

## b_append_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *[]int
var s = make([]int, 1, 4)

func inner() int { *p = append(s, 5, 6); return 0 }
func probe() int { show(inner); t := s[:3]; return t[1]*10 + t[2] }
func main() { show(probe) }
```

## b_append_niltarget2
```go
package main

var p *[]int
var s = make([]int, 1, 4)

func inner() { defer func() { recover() }(); *p = append(s, 5, 6) }
func probe() int { inner(); t := s[:3]; return t[1]*10 + t[2] }
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## b_assert_mid_store
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	a := [2]int{}
	var i interface{} = "s"
	var x int
	func() { defer func() { recover() }(); a[0], x = 1, i.(int) }()
	return a[0]*10 + x
}
func main() { show(probe) }
```

## b_call_nil_func
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int { var f func(int) int; return f(1) }
func main() { show(probe) }
```

## b_clear_nil_ok
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int { var s []int; clear(s); m := map[int]int{1: 2}; clear(m); return len(m) }
func main() { show(probe) }
```

## b_copy_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *int
var dst = make([]int, 3)

func inner() int { *p = copy(dst, []int{7, 8, 9}); return 0 }
func probe() int { show(inner); return dst[0]*100 + dst[1]*10 + dst[2] }
func main() { show(probe) }
```

## b_copy_niltarget2
```go
package main

var p *int
var dst = make([]int, 3)

func inner() { defer func() { recover() }(); *p = copy(dst, []int{7, 8, 9}) }
func probe() int { inner(); return dst[0]*100 + dst[1]*10 + dst[2] }
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## b_defer_nil_receiver
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

type T struct{ x int }

func (t T) Val() int { return t.x }

func probe() int {
	var p *T
	defer p.Val()
	return 1
}
func main() { show(probe) }
```

## b_index_oob_append
```go
package main

var a [2][]int
var s = make([]int, 1, 4)
var i = 5

func inner() { defer func() { recover() }(); a[i] = append(s, 5, 6) }
func probe() int { inner(); t := s[:3]; return t[1]*10 + t[2] }
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## b_makechan_badcap_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *chan int
var c = -2

func probe() int { *p = make(chan int, c); return 1 }
func main() { show(probe) }
```

## b_makechan_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *chan int

func probe() int { *p = make(chan int); return 1 }
func main() { show(probe) }
```

## b_makemap_hint_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *map[int]int
var h = 4

func probe() int { *p = make(map[int]int, h); return 1 }
func main() { show(probe) }
```

## b_makemap_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *map[int]int

func probe() int { *p = make(map[int]int); return 1 }
func main() { show(probe) }
```

## b_makeslice_badlen_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *[]int
var n = -1

func probe() int { *p = make([]int, n); return 1 }
func main() { show(probe) }
```

## b_makeslice_niltarget
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

var p *[]int

func probe() int { *p = make([]int, 3); return 1 }
func main() { show(probe) }
```

## b_mapassign_append_nilmap
```go
package main

var m map[int][]int
var s = make([]int, 1, 4)

func inner() { defer func() { recover() }(); m[0] = append(s, 5, 6) }
func probe() int { inner(); t := s[:3]; return t[1]*10 + t[2] }
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## b_multiassign_oob
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	a := [3]int{}
	j := 5
	func() { defer func() { recover() }(); a[0], a[j] = 1, 2 }()
	return a[0]
}
func main() { show(probe) }
```

## b_nilmap_write
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int { var m map[string]int; m["k"] = 1; return 0 }
func main() { show(probe) }
```

## b_nilptr_field
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

type T struct{ f int }

func probe() int { var p *T; p.f = 1; return 0 }
func main() { show(probe) }
```

## b_send_closed
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	ch := make(chan int, 2)
	close(ch)
	x := 0
	func() { defer func() { recover() }(); x = 1; ch <- 5 }()
	return x*10 + len(ch)
}
func main() { show(probe) }
```

## b_sort_ints
```go
package main

import "sort"

func probe() int { s := []int{3, 1, 2}; sort.Ints(s); return s[0]*100 + s[1]*10 + s[2] }
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## b_unseq_swap_oob
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	a := []int{1, 2, 3}
	b := []int{4, 5, 6}
	i := 7
	func() { defer func() { recover() }(); a[0], b[0] = b[i], a[0] }()
	return a[0]*10 + b[0]
}
func main() { show(probe) }
```

## d_atomic_nil
```go
package main

import "sync/atomic"

func probe() int {
	var p *int64
	func() { defer func() { recover() }(); atomic.AddInt64(p, 1) }()
	var x int64
	atomic.AddInt64(&x, 2)
	return int(x)
}
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## d_bytes_runes
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	b := []byte("héllo")
	r := []rune("héllo")
	b[0] = 'H'
	r[0] = 'J'
	return len(b)*100 + len(r)*10 + int(b[0]-'A') + int(r[0]-'A')
}
func main() { show(probe) }
```

## d_once_panic_then_do
```go
package main

import "sync"

func probe() int {
	var o sync.Once
	n := 0
	func() { defer func() { recover() }(); o.Do(func() { n++; panic("boom") }) }()
	o.Do(func() { n += 10 })
	return n
}
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## d_select_send_closed
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	ch := make(chan int, 1)
	close(ch)
	x := 0
	func() {
		defer func() { recover() }()
		select {
		case ch <- 1:
			x = 5
		}
	}()
	return x
}
func main() { show(probe) }
```

## d_send_closed_buf
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

func probe() int {
	ch := make(chan int, 3)
	ch <- 1
	close(ch)
	func() { defer func() { recover() }(); ch <- 2 }()
	return len(ch)
}
func main() { show(probe) }
```

## d_unlock_unlocked
```go
package main

import "sync"

func probe() int {
	var m sync.Mutex
	m.Unlock()
	return 1
}
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## d_wg_negative_recover
```go
package main

import "sync"

func probe() int {
	var wg sync.WaitGroup
	wg.Add(3)
	func() { defer func() { recover() }(); wg.Add(-5) }()
	wg.Add(2) // gc: -2 + 2 = 0 -> Wait returns; a rolled-back Add would leave 3 + 2 = 5 -> Wait deadlocks
	wg.Wait()
	return 1
}
func main() { defer func() { if r := recover(); r != nil { println("panic recovered") } }(); println(probe()) }
```

## d_wg_negative_wait
```go
package main

func show(f func() int) { defer func() { if r := recover(); r != nil { if e, ok := r.(error); ok { println("panic:", e.Error()) } else { println("panic:", r.(string)) } } }(); println(f()) }

import "sync"

func probe() int {
	var wg sync.WaitGroup
	wg.Add(1)
	func() { defer func() { recover() }(); wg.Add(-2) }()
	wg.Add(1) // gc: -1 + 1 = 0 -> Wait returns
	wg.Wait()
	return 7
}
func main() { show(probe) }
```

## smoke
```go
package main

func probe() int {
	a := [3]int{1, 2, 3}
	p := &a[2]
	*p = 9
	return a[0] + a[1] + a[2]
}

func oob() int {
	a := [3]int{1, 2, 3}
	i := 5
	a[i] = 1
	return a[0]
}

func main() {
	println(probe())
	defer func() { r := recover(); println("recovered:", r == nil); }()
	println(oob())
}
```

