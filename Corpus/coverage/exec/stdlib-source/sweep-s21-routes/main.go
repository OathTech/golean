package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group I: the source-through members on the other routes — function values, method values, a user generic, closures /
// defer / a goroutine, package-level initializers and init(), user interfaces satisfied by library types.
import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"slices"
	"strconv"
	"strings"
	"sync"
	"unicode/utf8"
)

var up = strings.ToUpper("ab\u00e9")
var num = strconv.Itoa(-42)
var en = errors.New("e")
var parsed, perr = strconv.Atoi("7")
var gb strings.Builder
var joined string

func init() {
	gb.WriteString(strings.Join([]string{"i", "n"}, "-"))
	joined = strings.Repeat(gb.String(), 2)
}

func apply[T any](f func(T) T, x T) T     { return f(x) }
func apply2[A, B any](f func(A) B, a A) B { return f(a) }

type stringer interface{ String() string }
type unwrapper interface{ Unwrap() error }

func funcValues() string {
	f1 := strings.ToUpper
	f2 := strconv.Itoa
	f3 := utf8.RuneLen
	f4 := bytes.Equal
	var f5 func([]int, int) bool = slices_contains
	return f1("x") + f2(3) + strconv.Itoa(f3('\u00e9')) + strconv.FormatBool(f4([]byte("a"), []byte("a"))) + strconv.FormatBool(f5([]int{1, 2}, 2))
}
func explicitInstValue() (bool, int) {
	f := slices.Contains[[]int, int]
	g := slices.Index[[]string, string]
	return f([]int{1, 2}, 2), g([]string{"a", "b"}, "b")
}
func slices_contains(s []int, v int) bool { return strings.Contains(fmt.Sprint(s), strconv.Itoa(v)) }
func methodValues() string {
	var b strings.Builder
	w := b.WriteString
	w("m")
	w("v")
	u := binary.LittleEndian.Uint16
	var buf bytes.Buffer
	wb := buf.WriteByte
	wb('q')
	return b.String() + strconv.Itoa(int(u([]byte{1, 2}))) + buf.String()
}
func genericApply() string {
	return apply(strings.ToUpper, "g") + apply2(strconv.Itoa, 9) + apply(strings.TrimSpace, "  t ") + strconv.FormatBool(apply2(utf8.ValidString, "\xff"))
}
func closureDeferGo() (out string) {
	var b strings.Builder
	add := func(s string) { b.WriteString(strings.ToUpper(s)) }
	defer func() { out = b.String() + "|" + out }()
	ch := make(chan string, 1)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { defer wg.Done(); ch <- strconv.Quote(strings.Repeat("g", 2)) }()
	wg.Wait()
	add("a")
	add("b")
	return <-ch
}
func initCalls() (string, string, string, int, bool, string, string) {
	return up, num, en.Error(), parsed, perr == nil, gb.String(), joined
}
func ifaceDispatch() string {
	var b strings.Builder
	b.WriteString("s")
	var s stringer = &b
	var buf bytes.Buffer
	var w interface{ WriteString(string) (int, error) } = &buf
	w.WriteString("w")
	_, err := strconv.ParseInt("x", 10, 64)
	var e error = err
	u := e.(unwrapper)
	return s.String() + buf.String() + "|" + e.Error() + "|" + strconv.FormatBool(u.Unwrap() == strconv.ErrSyntax)
}

func main() {
	funcValues()
	methodValues()
	genericApply()
	closureDeferGo()
	initCalls()
	ifaceDispatch()
	explicitInstValue()
}
