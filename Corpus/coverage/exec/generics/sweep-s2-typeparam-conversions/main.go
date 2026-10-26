package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Conversions whose operand or target is a TYPE PARAMETER (monomorphized before
// the emitter routes by underlying kind): []byte and []rune of a ~string
// parameter, string of a ~[]byte and of a ~byte|~rune parameter, a ~string
// parameter as the target, and the identity T(x) at several instantiations.

type MyS string
type MyB []byte
type MyRune rune
type A struct{ X int }
type B struct{ X int }

func (b B) Get() int { return b.X }

func bytesOf[S ~string](s S) []byte   { return []byte(s) }
func stringOf[B ~[]byte](b B) string  { return string(b) }
func runesOf[S ~string](s S) []rune   { return []rune(s) }
func toS[S ~string](x string) S       { return S(x) }
func fromS[S ~string](x S) string     { return string(x) }
func str[T ~byte | ~rune](x T) string { return string(x) }
func same[T any](x T) T               { return T(x) }

func bytesOfTypeParam() (int, int) {
	b := bytesOf(MyS("héllo"))
	c := bytesOf("ab")
	return len(b), len(c)
}

func stringOfTypeParamBytes() (string, bool) {
	s := stringOf(MyB([]byte("ok")))
	t := stringOf([]byte("x"))
	return s + t, s == "ok"
}

func runesOfTypeParam() (int, int) {
	r := runesOf(MyS("héllo"))
	return len(r), int(r[1])
}

func typeParamStringTarget() (int, string) {
	s := toS[MyS]("abc")
	var i any = s
	k := 0
	switch i.(type) {
	case string:
		k = 1
	case MyS:
		k = 2
	}
	return k, fromS(s)
}

func stringOfTypeParamInt() (string, int) {
	s := str(byte(65)) + str(MyRune(0x4E16)) + str(rune(-1))
	return s, len(s)
}

func identityTypeParamConv() int {
	i := same[any](3)
	s := same([]int{1, 2})
	b := same(B(A{4}))
	str := same("ab")
	n := same(5)
	r := 0
	if v, ok := i.(int); ok {
		r += v
	}
	return r*10000 + len(s)*1000 + b.Get()*100 + len(str)*10 + n
}

func main() {}
