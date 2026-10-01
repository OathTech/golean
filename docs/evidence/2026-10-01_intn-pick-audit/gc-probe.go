package main

import (
	"fmt"
	"math"
	"math/rand"
	v2 "math/rand/v2"
	"os"
)

func payload(f func()) (string, string) {
	var cls, txt string
	func() {
		defer func() {
			r := recover()
			switch v := r.(type) {
			case string:
				cls, txt = "string", v
			case error:
				cls, txt = fmt.Sprintf("error:%T", v), v.Error()
			default:
				cls, txt = fmt.Sprintf("other:%T", v), fmt.Sprint(v)
			}
		}()
		f()
	}()
	return cls, txt
}

func main() {
	for _, n := range []int{0, -1, -1 << 62} {
		c, t := payload(func() { rand.Intn(n) })
		fmt.Printf("v1 Intn(%d): %s %q\n", n, c, t)
		c, t = payload(func() { v2.IntN(n) })
		fmt.Printf("v2 IntN(%d): %s %q\n", n, c, t)
	}
	fmt.Println("Intn(1) x20:", func() (s []int) { for i := 0; i < 20; i++ { s = append(s, rand.Intn(1)) }; return }())
	ok := true
	for i := 0; i < 200000; i++ {
		if v := rand.Intn(5); v < 0 || v >= 5 { ok = false }
		if v := v2.IntN(3); v < 0 || v >= 3 { ok = false }
		if v := rand.Intn(math.MaxInt64); v < 0 { ok = false }
		if v := rand.Intn(1<<31 - 1); v < 0 || v >= 1<<31-1 { ok = false }
		if v := rand.Intn(1 << 31); v < 0 || v >= 1<<31 { ok = false }
	}
	fmt.Println("all draws in range:", ok)
	seen := map[int]bool{}
	for i := 0; i < 1000; i++ { seen[rand.Intn(5)] = true }
	fmt.Println("Intn(5) members seen:", len(seen))
	if len(os.Args) > 1 { rand.Intn(0) }
}
