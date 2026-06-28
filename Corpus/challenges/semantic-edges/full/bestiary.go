// bestiary.go -- a tour of Go semantic edge cases.
//
// This full program is a reference challenge corpus. It is intentionally not
// in the active Gobra/Lean differential manifest; promote cases one at a time
// when the frontend and GoCore semantics cover the relevant feature.
package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"strings"
	"sync"
	"unicode/utf8"
	"unsafe"
)

var derived = base + 1
var base = 10
var initFlag string

func init() { initFlag = "init() ran before main()" }

func banner(n int, title string) {
	fmt.Printf("\n%02d. %s\n%s\n", n, title, strings.Repeat("-", 64))
}

func sec(title string) {
	fmt.Printf("\n========== %s ==========\n", strings.ToUpper(title))
}

func safe(f func()) {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("    >> recovered panic: %v\n", r)
		}
	}()
	f()
}

type beeper interface{ beep() string }
type device struct{}

func (d *device) beep() string { return "beep" }

func c01_methodSet() {
	banner(1, "Pointer-receiver methods are NOT in a value's method set")
	var asValue any = device{}
	var asPtr any = &device{}
	_, okValue := asValue.(beeper)
	_, okPtr := asPtr.(beeper)
	fmt.Printf("    device{} implements beeper? %v\n", okValue)
	fmt.Printf("    &device{} implements beeper? %v\n", okPtr)
}

func c02_interfaceCompareDiffTypes() {
	banner(2, "Interfaces of different dynamic types compare false")
	var a, b any = 1, "1"
	var c, d any = 1, 1
	fmt.Printf("    any(1) == any(\"1\")? %v\n", a == b)
	fmt.Printf("    any(1) == any(1)? %v\n", c == d)
}

func c03_typeSwitchNil() {
	banner(3, "A type switch matches case nil for a nil interface")
	var x any
	got := ""
	switch x.(type) {
	case nil:
		got = "nil"
	case int:
		got = "int"
	default:
		got = "other"
	}
	fmt.Printf("    switch on nil interface -> case %s\n", got)
}

type animal struct{}

func (animal) sound() string { return "generic noise" }

type dog struct{ animal }
type noisemaker interface{ sound() string }

func c04_embeddingPromotes() {
	banner(4, "Embedding promotes methods")
	d := dog{}
	var nm noisemaker = dog{}
	fmt.Printf("    dog{}.sound() = %q\n", d.sound())
	fmt.Printf("    dog satisfies noisemaker: %q\n", nm.sound())
}

type baseRec struct{ name string }
type wrapper struct {
	baseRec
	name string
}

func c05_embeddedShadow() {
	banner(5, "An outer field shadows an embedded field")
	w := wrapper{}
	w.name = "outer"
	w.baseRec.name = "inner"
	fmt.Printf("    w.name=%q w.baseRec.name=%q\n", w.name, w.baseRec.name)
}

func c06_emptyStruct() {
	banner(6, "The empty struct occupies zero bytes")
	type twoEmpties struct{ a, b struct{} }
	fmt.Printf("    sizeof(struct{}{}) = %d\n", unsafe.Sizeof(struct{}{}))
	fmt.Printf("    sizeof(twoEmpties{}) = %d\n", unsafe.Sizeof(twoEmpties{}))
}

func c07_constArbitraryPrecision() {
	banner(7, "Untyped constants have arbitrary precision until used")
	const huge = 1 << 100
	const back = huge >> 100
	fmt.Printf("    (1<<100)>>100 = %d\n", back)
}

func c08_iotaBlank() {
	banner(8, "iota keeps counting through blank identifiers")
	const (
		zero = iota
		_
		two
		_
		four
	)
	fmt.Printf("    zero=%d two=%d four=%d\n", zero, two, four)
}

func c09_untypedConstAdapts() {
	banner(9, "An untyped constant adapts to the context")
	const k = 42
	var f float64 = k
	var i int = k
	var b byte = k
	var r rune = k
	fmt.Printf("    float64=%v int=%d byte=%d rune=%d\n", f, i, b, r)
}

func c10_constDivision() {
	banner(10, "Constant division follows operand types")
	const intDiv = 1 / 3
	const floatDiv = 1.0 / 3
	fmt.Printf("    1 / 3 = %v; 1.0 / 3 = %v\n", intDiv, floatDiv)
}

func c11_defaultConstTypes() {
	banner(11, "Untyped literals have default types")
	fmt.Printf("    %%T of 'a', 3, 3.0, 3i = %T, %T, %T, %T\n", 'a', 3, 3.0, 3i)
}

func c12_indexStringIsByte() {
	banner(12, "Indexing a string yields a byte")
	s := "abc"
	fmt.Printf("    s[0]=%d (%T), as char %q\n", s[0], s[0], rune(s[0]))
}

func c13_sliceSplitsRune() {
	banner(13, "Slicing a string is by bytes")
	s := "hello"
	s = "h" + string([]byte{0xc3, 0xa9}) + s[2:]
	bad := s[0:2]
	fmt.Printf("    s[0:2]=%q valid UTF-8? %v\n", bad, utf8.ValidString(bad))
}

func c14_bytesVsRunes() {
	banner(14, "len() counts bytes, not characters")
	s := "hello"
	s = "h" + string([]byte{0xc3, 0xa9}) + s[2:]
	fmt.Printf("    len(%q)=%d bytes, runes=%d\n", s, len(s), utf8.RuneCountInString(s))
}

func c15_deleteNilMap() {
	banner(15, "delete() on a nil map is a no-op")
	var m map[string]int
	delete(m, "missing")
	fmt.Printf("    delete(nilMap, k) did not panic; len=%d\n", len(m))
}

type ctr struct{ n int }

func c16_mapElementNotAddressable() {
	banner(16, "Map elements are not addressable")
	m := map[string]ctr{"a": {n: 1}}
	v := m["a"]
	v.n++
	m["a"] = v
	fmt.Printf("    m[\"a\"].n = %d\n", m["a"].n)
}

func c17_slicesMapsOnlyCompareNil() {
	banner(17, "Slices and maps are only comparable to nil")
	var s []int
	var m map[int]int
	fmt.Printf("    s == nil? %v; m == nil? %v\n", s == nil, m == nil)
}

func c18_resliceIntoCapacity() {
	banner(18, "You can reslice beyond len, up to cap")
	a := make([]int, 2, 5)
	b := a[:5]
	fmt.Printf("    len(a)=%d cap(a)=%d len(a[:5])=%d\n", len(a), cap(a), len(b))
}

func c19_arraysComparable() {
	banner(19, "Arrays are comparable")
	x := [3]int{1, 2, 3}
	y := [3]int{1, 2, 3}
	fmt.Printf("    x == y? %v\n", x == y)
}

func c20_makeLenGtCap() {
	banner(20, "make([]T, len, cap) with len > cap panics")
	length, capacity := 5, 3
	safe(func() { _ = make([]int, length, capacity) })
}

func grow(s []int)     { s = append(s, 99); _ = s }
func setFirst(s []int) { s[0] = 99 }

func c21_sliceHeaderByValue() {
	banner(21, "A slice header is passed by value")
	a := []int{1, 2, 3}
	grow(a)
	fmt.Printf("    after grow(a): %v\n", a)
	setFirst(a)
	fmt.Printf("    after setFirst(a): %v\n", a)
}

func c22_nilVsEmptySlice() {
	banner(22, "nil slice vs empty slice")
	var nilSlice []int
	emptySlice := []int{}
	fmt.Printf("    nil len=%d ==nil? %v\n", len(nilSlice), nilSlice == nil)
	fmt.Printf("    empty len=%d ==nil? %v\n", len(emptySlice), emptySlice == nil)
}

func c23_divByZero() {
	banner(23, "Integer /0 panics; float /0 yields Inf/NaN")
	zeroInt := 0
	safe(func() { _ = 1 / zeroInt })
	var zeroFloat float64 = 0
	fmt.Printf("    1.0/0.0=%v; 0.0/0.0=%v\n", 1/zeroFloat, zeroFloat/zeroFloat)
}

func c24_complementNoPower() {
	banner(24, "^ is bitwise complement")
	fmt.Printf("    ^0=%d; ^uint8(0)=%d\n", ^0, ^uint8(0))
}

func c25_bitClear() {
	banner(25, "&^ is the bit-clear operator")
	const flags = 0b1111
	const mask = 0b0101
	fmt.Printf("    0b1111 &^ 0b0101 = %04b (%d)\n", flags&^mask, flags&^mask)
}

func c26_noImplicitConversion() {
	banner(26, "No implicit numeric conversion")
	var i int = 3
	var f float64 = 1.5
	result := float64(i) * f
	fmt.Printf("    float64(i) * f = %v\n", result)
}

func c27_builtinComplex() {
	banner(27, "Complex numbers are built in")
	c := complex(2, 3)
	fmt.Printf("    c=%v real=%v imag=%v c*c=%v\n", c, real(c), imag(c), c*c)
}

func c28_noFallthrough() {
	banner(28, "switch cases do not fall through by default")
	var withoutFT []string
	switch 1 {
	case 1:
		withoutFT = append(withoutFT, "1")
	case 2:
		withoutFT = append(withoutFT, "2")
	}
	var withFT []string
	switch 1 {
	case 1:
		withFT = append(withFT, "1")
		fallthrough
	case 2:
		withFT = append(withFT, "2")
	case 3:
		withFT = append(withFT, "3")
	}
	fmt.Printf("    no fallthrough=%v; with fallthrough=%v\n", withoutFT, withFT)
}

func c29_exprlessSwitch() {
	banner(29, "switch with no expression replaces if/else")
	classify := func(n int) string {
		switch {
		case n < 0:
			return "negative"
		case n == 0:
			return "zero"
		default:
			return "positive"
		}
	}
	bucket := ""
	switch 3 {
	case 1, 2, 3:
		bucket = "small"
	case 4, 5, 6:
		bucket = "medium"
	}
	fmt.Printf("    classify(-2)=%s classify(0)=%s bucket=%s\n", classify(-2), classify(0), bucket)
}

func c30_rangeOverInt() {
	banner(30, "Go 1.22+: range over an integer")
	var got []int
	for i := range 3 {
		got = append(got, i)
	}
	fmt.Printf("    range 3 -> %v\n", got)
}

func c31_rangeOverFunc() {
	banner(31, "Go 1.23+: range over a function")
	seq := func(yield func(int) bool) {
		for i := 0; i < 3; i++ {
			if !yield(i * i) {
				return
			}
		}
	}
	var got []int
	seq(func(v int) bool { got = append(got, v); return true })
	fmt.Printf("    iterator yielded -> %v\n", got)
}

func c32_initStatementScope() {
	banner(32, "if init variables are scoped through else")
	msg := ""
	if v := 3; v > 5 {
		msg = fmt.Sprintf("big (%d)", v)
	} else {
		msg = fmt.Sprintf("small (%d)", v)
	}
	fmt.Printf("    %s\n", msg)
}

func c33_shortDeclMixing() {
	banner(33, ":= may reuse existing variables if one is new")
	a := 1
	a, b := 2, 3
	fmt.Printf("    a=%d b=%d\n", a, b)
}

func c34_labeledContinue() {
	banner(34, "Labeled continue jumps to an outer loop")
	var pairs []string
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
			pairs = append(pairs, fmt.Sprintf("%d-%d", i, j))
		}
	}
	fmt.Printf("    collected -> %v\n", pairs)
}

func c35_oneLoopKeyword() {
	banner(35, "for is the only loop keyword")
	n := 0
	for n < 3 {
		n++
	}
	fmt.Printf("    n=%d\n", n)
}

func c36_panicNil() {
	banner(36, "panic(nil) is converted to a non-nil error in modern Go")
	got := func() (typ string) {
		defer func() { typ = fmt.Sprintf("%T", recover()) }()
		panic(nil)
	}()
	fmt.Printf("    recover type: %s\n", got)
}

func c37_deferRunsWhilePanicking() {
	banner(37, "Deferred calls run during panic unwinding")
	safe(func() {
		defer fmt.Println("    defer ran during unwinding")
		panic("boom")
	})
}

func c38_goroutinePanicNeedsOwnRecover() {
	banner(38, "Each goroutine must recover its own panic")
	done := make(chan string, 1)
	go func() {
		defer func() {
			if r := recover(); r != nil {
				done <- fmt.Sprintf("self-recovered: %v", r)
			}
		}()
		panic("inside goroutine")
	}()
	fmt.Printf("    %s\n", <-done)
}

func c39_zeroValueUsable() {
	banner(39, "Some zero values are ready to use")
	var mu sync.Mutex
	mu.Lock()
	mu.Unlock()
	var buf bytes.Buffer
	buf.WriteString("hi")
	fmt.Printf("    zero buffer holds %q\n", buf.String())
}

func c40_bufferedChannel() {
	banner(40, "A buffered channel blocks sends only when full")
	ch := make(chan int, 1)
	ch <- 1
	full := false
	select {
	case ch <- 2:
	default:
		full = true
	}
	fmt.Printf("    second send would block? %v\n", full)
}

func c41_rangeOverChannel() {
	banner(41, "range over channel receives until closed")
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	close(ch)
	sum := 0
	for v := range ch {
		sum += v
	}
	fmt.Printf("    sum=%d\n", sum)
}

func c42_syncOnce() {
	banner(42, "sync.Once runs its function exactly once")
	var once sync.Once
	calls := 0
	for i := 0; i < 5; i++ {
		once.Do(func() { calls++ })
	}
	fmt.Printf("    calls=%d\n", calls)
}

func c43_unusedLocal() {
	banner(43, "Unused local variables are compile errors")
	x := 5
	_ = x
	fmt.Printf("    blank assignment makes x legal\n")
}

func c44_initOrder() {
	banner(44, "Package vars initialize in dependency order")
	fmt.Printf("    derived=%d; %s\n", derived, initFlag)
}

func c45_identityComparison() {
	banner(45, "Channels and pointers compare by identity")
	ch1 := make(chan int)
	ch2 := make(chan int)
	p := new(int)
	fmt.Printf("    ch1==ch1? %v ch1==ch2? %v\n", ch1 == ch1, ch1 == ch2)
	fmt.Printf("    new(int)==new(int)? %v p==p? %v\n", new(int) == new(int), p == p)
}

type meters int

func (m meters) String() string { return fmt.Sprintf("%dm", int(m)) }

func c46_verbVsStringer() {
	banner(46, "%v/%s call String(); %d does not")
	m := meters(5)
	fmt.Printf("    %%v=%v %%s=%s %%d=%d\n", m, m, m)
}

func c47_bytesPrinting() {
	banner(47, "A []byte prints as text with %s but numbers with %v")
	b := []byte("Hi")
	fmt.Printf("    %%s -> %s; %%v -> %v\n", b, b)
}

func c48_wrongVerb() {
	banner(48, "A wrong format verb annotates output instead of panicking")
	verb := "%d"
	fmt.Printf("    %q\n", fmt.Sprintf(verb, "hello"))
}

type xy struct{ X, Y int }

func c49_structVerbs() {
	banner(49, "%v, %+v and %#v render structs differently")
	p := xy{1, 2}
	fmt.Printf("    %%v=%v %%+v=%+v %%#v=%#v\n", p, p, p)
}

func c50_errorsNewDistinct() {
	banner(50, "errors.New returns a fresh distinct value")
	e1 := errors.New("duplicate")
	e2 := errors.New("duplicate")
	fmt.Printf("    e1==e2? %v; e1==e1? %v\n", e1 == e2, e1 == e1)
}

func c51_errorsIs() {
	banner(51, "errors.Is walks the %w wrap chain")
	notFound := errors.New("not found")
	wrapped := fmt.Errorf("loading user: %w", notFound)
	fmt.Printf("    wrapped==notFound? %v; errors.Is? %v\n", wrapped == notFound, errors.Is(wrapped, notFound))
}

func c52_closuresShare() {
	banner(52, "Closures capture variables by reference")
	x := 0
	inc := func() { x++ }
	read := func() int { return x }
	inc()
	inc()
	fmt.Printf("    read()=%d\n", read())
}

type vec struct{ x int }

func (v vec) val() int { return v.x }

func c53_methodExpression() {
	banner(53, "A method expression makes receiver the first argument")
	f := vec.val
	fmt.Printf("    f(vec{7})=%d\n", f(vec{7}))
}

func split(sum int) (a, b int) {
	a = sum * 4 / 9
	b = sum - a
	return
}

func c54_nakedReturn() {
	banner(54, "Named return values are returned by bare return")
	a, b := split(17)
	fmt.Printf("    split(17) -> %d %d\n", a, b)
}

func isNilArgs(xs ...int) bool { return xs == nil }

func c55_variadicNil() {
	banner(55, "Calling a variadic func with no args yields a nil slice")
	fmt.Printf("    no args nil? %v; one arg nil? %v\n", isNilArgs(), isNilArgs(1))
}

func mapSlice[T, U any](s []T, f func(T) U) []U {
	out := make([]U, len(s))
	for i, v := range s {
		out[i] = f(v)
	}
	return out
}

func c56_noGenericMethods() {
	banner(56, "Top-level funcs can be generic; methods cannot have type params")
	squares := mapSlice([]int{1, 2, 3}, func(i int) int { return i * i })
	fmt.Printf("    squares=%v\n", squares)
}

func indexOf[T comparable](s []T, v T) int {
	for i, x := range s {
		if x == v {
			return i
		}
	}
	return -1
}

func c57_comparableAndInference() {
	banner(57, "comparable constraint plus type inference")
	fmt.Printf("    index=%d\n", indexOf([]string{"a", "b", "c"}, "b"))
}

func zeroOf[T any]() T {
	var z T
	return z
}

func c58_typeParamZero() {
	banner(58, "var z T gives zero value of a type parameter")
	fmt.Printf("    int=%d string=%q bool=%v\n", zeroOf[int](), zeroOf[string](), zeroOf[bool]())
}

type record struct {
	Public  int
	private int
}

func c59_visibilityByCase() {
	banner(59, "Identifier case controls export")
	b, _ := json.Marshal(record{Public: 1, private: 2})
	fmt.Printf("    json=%s\n", b)
}

func c60_newVsMake() {
	banner(60, "new(map) gives a nil map; make returns a writable one")
	p := new(map[string]int)
	fmt.Printf("    *new(map[string]int) == nil? %v\n", *p == nil)
	safe(func() { (*p)["k"] = 1 })
	m := make(map[string]int)
	m["k"] = 1
	fmt.Printf("    make map m[\"k\"]=%d\n", m["k"])
}

func main() {
	fmt.Println("Go bestiary -- a tour of semantic edge cases")
	sec("types, interfaces, method sets")
	c01_methodSet()
	c02_interfaceCompareDiffTypes()
	c03_typeSwitchNil()
	c04_embeddingPromotes()
	c05_embeddedShadow()
	c06_emptyStruct()
	sec("constants")
	c07_constArbitraryPrecision()
	c08_iotaBlank()
	c09_untypedConstAdapts()
	c10_constDivision()
	c11_defaultConstTypes()
	sec("strings, bytes, runes")
	c12_indexStringIsByte()
	c13_sliceSplitsRune()
	c14_bytesVsRunes()
	sec("slices, arrays, maps")
	c15_deleteNilMap()
	c16_mapElementNotAddressable()
	c17_slicesMapsOnlyCompareNil()
	c18_resliceIntoCapacity()
	c19_arraysComparable()
	c20_makeLenGtCap()
	c21_sliceHeaderByValue()
	c22_nilVsEmptySlice()
	sec("numbers and operators")
	c23_divByZero()
	c24_complementNoPower()
	c25_bitClear()
	c26_noImplicitConversion()
	c27_builtinComplex()
	sec("control flow")
	c28_noFallthrough()
	c29_exprlessSwitch()
	c30_rangeOverInt()
	c31_rangeOverFunc()
	c32_initStatementScope()
	c33_shortDeclMixing()
	c34_labeledContinue()
	c35_oneLoopKeyword()
	sec("defer, panic, recover")
	c36_panicNil()
	c37_deferRunsWhilePanicking()
	c38_goroutinePanicNeedsOwnRecover()
	sec("concurrency")
	c39_zeroValueUsable()
	c40_bufferedChannel()
	c41_rangeOverChannel()
	c42_syncOnce()
	sec("zero values and initialization")
	c43_unusedLocal()
	c44_initOrder()
	sec("equality and identity")
	c45_identityComparison()
	sec("fmt and printing")
	c46_verbVsStringer()
	c47_bytesPrinting()
	c48_wrongVerb()
	c49_structVerbs()
	sec("errors")
	c50_errorsNewDistinct()
	c51_errorsIs()
	sec("closures and functions")
	c52_closuresShare()
	c53_methodExpression()
	c54_nakedReturn()
	c55_variadicNil()
	sec("generics")
	c56_noGenericMethods()
	c57_comparableAndInference()
	c58_typeParamZero()
	sec("visibility and allocation")
	c59_visibilityByCase()
	c60_newVsMake()
	fmt.Println()
}
