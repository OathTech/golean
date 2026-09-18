// NaN latitude probe (records lane records/nan-envelope-memo-0918, [AGENT]).
// Run under the pinned oracle: go1.26.5 linux/amd64, default GOAMD64 (v1).
// Every operand is a VARIABLE (a constant NaN is a compile error), and each
// case is also routed through a noinline helper so the SSA operand order
// is the source order at the call boundary.
package main

import (
	"fmt"
	"math"
	"strconv"
)

//go:noinline
func add(a, b float64) float64 { return a + b }

//go:noinline
func sub(a, b float64) float64 { return a - b }

//go:noinline
func mul(a, b float64) float64 { return a * b }

//go:noinline
func div(a, b float64) float64 { return a / b }

//go:noinline
func add32(a, b float32) float32 { return a + b }

//go:noinline
func mn(a, b float64) float64 { return min(a, b) }

//go:noinline
func mx(a, b float64) float64 { return max(a, b) }

//go:noinline
func to32(a float64) float32 { return float32(a) }

//go:noinline
func to64(a float32) float64 { return float64(a) }

func b(f float64) string { return fmt.Sprintf("0x%016X", math.Float64bits(f)) }
func b32(f float32) string { return fmt.Sprintf("0x%08X", math.Float32bits(f)) }

func main() {
	z := 0.0
	one := 1.0
	inf := math.Inf(1)
	p := math.Float64frombits(0x7FF8000000000001) // math.NaN()'s pattern
	q := math.Float64frombits(0x7FF8000000000002) // a second payload
	s := math.Float64frombits(0x7FF0000000000001) // signalling NaN
	nq := math.Float64frombits(0xFFF8000000000001) // negative quiet, payload 1

	fmt.Println("== generation (invalid operations) ==")
	fmt.Println("math.NaN()        ", b(math.NaN()))
	fmt.Println("z/z               ", b(z/z))
	fmt.Println("div(z,z)          ", b(div(z, z)))
	fmt.Println("-(z/z)            ", b(-(z / z)))
	fmt.Println("inf-inf           ", b(sub(inf, inf)))
	fmt.Println("inf*0             ", b(mul(inf, z)))
	fmt.Println("0*inf             ", b(mul(z, inf)))
	fmt.Println("inf/inf           ", b(div(inf, inf)))
	fmt.Println("math.Sqrt(-1)     ", b(math.Sqrt(-one)))

	fmt.Println("== propagation: one NaN operand ==")
	fmt.Println("p+1  inline       ", b(p+one))
	fmt.Println("1+p  inline       ", b(one+p))
	fmt.Println("add(p,1)          ", b(add(p, one)))
	fmt.Println("add(1,p)          ", b(add(one, p)))
	fmt.Println("mul(p,2)          ", b(mul(p, 2)))
	fmt.Println("mul(2,p)          ", b(mul(2, p)))
	fmt.Println("div(p,2)          ", b(div(p, 2)))
	fmt.Println("div(2,p)          ", b(div(2, p)))
	fmt.Println("sub(1,p)          ", b(sub(one, p)))
	fmt.Println("nq+1              ", b(add(nq, one)))

	fmt.Println("== propagation: two NaN operands (which payload?) ==")
	fmt.Println("p+q  inline       ", b(p+q))
	fmt.Println("q+p  inline       ", b(q+p))
	fmt.Println("add(p,q)          ", b(add(p, q)))
	fmt.Println("add(q,p)          ", b(add(q, p)))
	fmt.Println("mul(p,q)          ", b(mul(p, q)))
	fmt.Println("mul(q,p)          ", b(mul(q, p)))
	fmt.Println("sub(p,q)          ", b(sub(p, q)))
	fmt.Println("sub(q,p)          ", b(sub(q, p)))
	fmt.Println("div(p,q)          ", b(div(p, q)))
	fmt.Println("div(q,p)          ", b(div(q, p)))

	fmt.Println("== signalling NaN operand (quieting) ==")
	fmt.Println("s                 ", b(s))
	fmt.Println("add(s,1)          ", b(add(s, one)))
	fmt.Println("add(1,s)          ", b(add(one, s)))
	fmt.Println("add(s,p)          ", b(add(s, p)))
	fmt.Println("add(p,s)          ", b(add(p, s)))

	fmt.Println("== negation ==")
	fmt.Println("-p                ", b(-p))
	fmt.Println("-nq               ", b(-nq))
	fmt.Println("math.Abs(z/z)     ", b(math.Abs(z/z)))

	fmt.Println("== min / max ==")
	fmt.Println("min(z/z,2.5)      ", b(mn(z/z, 2.5)))
	fmt.Println("max(z/z,2.5)      ", b(mx(z/z, 2.5)))
	fmt.Println("min(p,2.5)        ", b(mn(p, 2.5)))
	fmt.Println("min(2.5,p)        ", b(mn(2.5, p)))
	fmt.Println("min(p,q)          ", b(mn(p, q)))
	fmt.Println("min(q,p)          ", b(mn(q, p)))
	fmt.Println("max(p,2.5)        ", b(mx(p, 2.5)))

	fmt.Println("== float32 ==")
	var z32 float32
	var one32 float32 = 1
	p32 := math.Float32frombits(0x7FC00001)
	fmt.Println("z32/z32           ", b32(z32/z32))
	fmt.Println("-(z32/z32)        ", b32(-(z32 / z32)))
	fmt.Println("add32(p32,1)      ", b32(add32(p32, one32)))
	fmt.Println("add32(1,p32)      ", b32(add32(one32, p32)))
	fmt.Println("float32(p)        ", b32(to32(p)))
	fmt.Println("float32(q<<)      ", b32(to32(math.Float64frombits(0x7FF8000020000000))))
	fmt.Println("float32(z/z)      ", b32(to32(z/z)))
	fmt.Println("float64(p32)      ", b(to64(p32)))
	fmt.Println("float64(z32/z32)  ", b(to64(z32/z32)))

	fmt.Println("== observability through other channels ==")
	n := z / z
	fmt.Println("fmt %v            ", fmt.Sprintf("%v %v", n, -n))
	fmt.Println("fmt %g %e %f      ", fmt.Sprintf("%g %e %f", n, n, n))
	fmt.Println("fmt %b %x %X      ", fmt.Sprintf("%b %x %X", n, n, n))
	fmt.Println("fmt %v of p       ", fmt.Sprintf("%v %b", p, p))
	fmt.Println("strconv 'g' n,-n  ", strconv.FormatFloat(n, 'g', -1, 64), strconv.FormatFloat(-n, 'g', -1, 64))
	fmt.Println("strconv 'b' n     ", strconv.FormatFloat(n, 'b', -1, 64))
	print("println(n) -> ")
	println(n)
	print("println(-n) -> ")
	println(-n)
	fmt.Println("Signbit(n) Signbit(-n)", math.Signbit(n), math.Signbit(-n))
	fmt.Println("n==n, n!=n        ", n == n, n != n)
	fmt.Println("any(n)==any(n)    ", any(n) == any(n))
	m := map[float64]int{}
	m[n] = 1
	m[n] = 2
	m[p] = 3
	fmt.Println("len(map after 3 NaN inserts)", len(m))
	fmt.Println("IsNaN(n) IsNaN(p) IsNaN(nq)", math.IsNaN(n), math.IsNaN(p), math.IsNaN(nq))
}
