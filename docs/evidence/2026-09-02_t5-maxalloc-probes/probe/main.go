// gc probe: the maxAlloc panic class (t5-maxalloc, 2026-09-02). One probe
// per invocation (fatal errors kill the process), selected by os.Args[1].
// Uses unsafe ONLY to build a large-length slice header for the append
// probes without materializing memory — gc-only subject, not a machine one.
package main

import (
	"fmt"
	"os"
	"runtime"
	"sync"
	"unsafe"
)

func report(name string, f func()) {
	defer func() {
		r := recover()
		if r == nil {
			fmt.Printf("%-28s NO PANIC\n", name)
			return
		}
		_, isRE := r.(runtime.Error)
		fmt.Printf("%-28s PANIC runtime.Error=%v msg=%q type=%T\n", name, isRE, fmt.Sprint(r), r)
	}()
	f()
}

var sink interface{}

func main() {
	n48 := 1 << 48
	n48p1 := n48 + 1
	n45 := 1 << 45
	neg := -1
	n62 := 1 << 62
	hint := n48p1
	name := os.Args[1]
	switch name {
	case "slice-len-over-var":
		report(name, func() { sink = make([]byte, n48p1) })
	case "slice-len-over-const":
		report(name, func() { sink = make([]byte, 1<<48+1) })
	case "slice-len-eq-maxalloc":
		report(name, func() { sink = make([]byte, n48) }) // mem == maxAlloc: expect fatal OOM, not panic
	case "slice-int64-over":
		report(name, func() { sink = make([]int64, n45+1) })
	case "slice-int64-eq":
		report(name, func() { sink = make([]int64, n45) }) // mem == maxAlloc: expect fatal OOM
	case "slice-cap-over":
		report(name, func() { sink = make([]byte, 0, n48p1) })
	case "slice-len-and-cap-over":
		report(name, func() { sink = make([]byte, n48p1+1, n48p1) })
	case "slice-len-gt-cap":
		report(name, func() { sink = make([]byte, 5, n48p1-n48) })
	case "slice-len-neg":
		report(name, func() { sink = make([]byte, neg) })
	case "slice-cap-neg":
		report(name, func() { sink = make([]byte, 0, neg) })
	case "slice-struct0-huge":
		report(name, func() { s := make([]struct{}, n62); fmt.Println(len(s), cap(s)) })
	case "slice-int32-over":
		report(name, func() { sink = make([]int32, (n48>>2)+1) })
	case "slice-3byte-over":
		report(name, func() { sink = make([][3]byte, n48/3+1) }) // 3*(n48/3+1) > maxAlloc
	case "slice-3byte-eq":
		report(name, func() { sink = make([][3]byte, n48/3) }) // 3*(n48/3) = maxAlloc-1: expect fatal OOM
	case "chan-byte-over":
		report(name, func() { sink = make(chan byte, n48) })
	case "chan-byte-boundary-panic":
		report(name, func() { sink = make(chan byte, n48-95) }) // mem = maxAlloc-95 > maxAlloc-hchanSize(96)
	case "chan-byte-boundary-ok":
		report(name, func() { sink = make(chan byte, n48-96) }) // mem = maxAlloc-96: expect fatal OOM
	case "chan-int64-over":
		report(name, func() { sink = make(chan int64, n45) })
	case "chan-struct0-huge":
		report(name, func() { c := make(chan struct{}, n62); fmt.Println(cap(c)) })
	case "chan-neg":
		report(name, func() { sink = make(chan byte, neg) })
	case "map-hint-over":
		report(name, func() { m := make(map[int]int, hint); m[1] = 2; fmt.Println(len(m)) })
	case "map-hint-neg":
		report(name, func() { m := make(map[int]int, neg); m[1] = 2; fmt.Println(len(m)) })
	case "append-growth-over-unsafe":
		report(name, func() {
			var x byte
			s := unsafe.Slice(&x, n48-1)
			s = append(s, 7)
			fmt.Println(len(s))
		})
	case "append-int64-over-unsafe":
		report(name, func() {
			var x int64
			s := unsafe.Slice(&x, n45-1)
			s = append(s, 7)
			fmt.Println(len(s))
		})
	case "append-newlen-overflow":
		report(name, func() {
			s := make([]struct{}, n62)
			s = append(s, s...)
			fmt.Println(len(s))
			s = append(s, s...)
			fmt.Println(len(s))
		})
	case "recover-error-iface":
		report(name, func() {
			defer func() {
				r := recover()
				e, ok := r.(error)
				fmt.Println("recover: error?", ok, e.Error())
				panic(r)
			}()
			sink = make([]byte, n48p1)
		})
	case "uncaught":
		sink = make([]byte, n48p1)
	case "chan-byte-n": // second arg: offset below 1<<48
		off := 0
		fmt.Sscan(os.Args[2], &off)
		report(name+" "+os.Args[2], func() { sink = make(chan byte, n48-off) })
	case "sizes":
		fmt.Println("sync.Mutex", unsafe.Sizeof(sync.Mutex{}), "align", unsafe.Alignof(sync.Mutex{}))
		fmt.Println("sync.RWMutex", unsafe.Sizeof(sync.RWMutex{}), "align", unsafe.Alignof(sync.RWMutex{}))
		fmt.Println("sync.WaitGroup", unsafe.Sizeof(sync.WaitGroup{}), "align", unsafe.Alignof(sync.WaitGroup{}))
		fmt.Println("sync.Once", unsafe.Sizeof(sync.Once{}), "align", unsafe.Alignof(sync.Once{}))
		var e error
		var a any
		fmt.Println("string", unsafe.Sizeof(""), "slice", unsafe.Sizeof([]byte{}), "iface", unsafe.Sizeof(a), "error", unsafe.Sizeof(e))
		fmt.Println("map", unsafe.Sizeof(map[int]int{}), "chan", unsafe.Sizeof(make(chan int)), "func", unsafe.Sizeof(func() {}), "ptr", unsafe.Sizeof(&a))
		fmt.Println("complex64", unsafe.Sizeof(complex64(0)), "align", unsafe.Alignof(complex64(0)), "complex128", unsafe.Sizeof(complex128(0)), "align", unsafe.Alignof(complex128(0)))
		type s1 struct {
			a int64
			b byte
		}
		type s2 struct {
			a byte
			b int64
			c byte
		}
		type s3 struct {
			a int64
			z struct{}
		}
		type s4 struct{ z struct{} }
		type s5 struct {
			a [3]byte
			b int32
		}
		type s6 struct {
			a int32
			b [0]int64
		}
		fmt.Println("s1{int64,byte}", unsafe.Sizeof(s1{}), "s2{byte,int64,byte}", unsafe.Sizeof(s2{}), "s3{int64,struct{}}", unsafe.Sizeof(s3{}), "s4{struct{}}", unsafe.Sizeof(s4{}), "s5{[3]byte,int32}", unsafe.Sizeof(s5{}), "s6{int32,[0]int64}", unsafe.Sizeof(s6{}), "align s6", unsafe.Alignof(s6{}))
	default:
		fmt.Println("unknown probe", name)
		os.Exit(2)
	}
}
