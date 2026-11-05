// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Conversions spelled with a
// PARENTHESISED type at every target kind beyond the covered (*T)/(<-chan)/(func())/(int)
// forms; expected = gc go1.26.5.

package main

type myInt int
type pair struct{ a, b int }
type pair2 struct{ a, b int }
type namer interface{ name() string }
type cat struct{}

func (cat) name() string { return "cat" }

func parenTypeConversions() int {
	s := "hé"
	b := ([]byte)(s)
	r := ([]rune)(s)
	back := (string)(b)
	fromR := (string)(r)
	one := (string)(rune(65))
	mi := (myInt)(5)
	p := (pair2)(pair{1, 2})
	sl := []int{7, 8}
	arr := [2]int{sl[0], sl[1]}
	var a any = (any)(mi)
	var e error = (error)(nil)
	m := (map[string]int)(map[string]int{"k": 3})
	ch := (chan int)(make(chan int, 1))
	ch <- 9
	x := 4
	px := &x
	pp := (**int)(&px)
	f := (func(int) int)(func(k int) int { return k * 2 })
	st := pair{3, 4}
	fl := (float64)(x)
	big := x + 296
	i8 := (int8)(big)
	u8 := (uint8)(x + 251)
	rn := (rune)(x + 61)
	var nm namer = (namer)(cat{})
	n := len(b)*1000000 + len(r)*100000 + len(back)*10000 + len(fromR)*1000 + len(one)*100
	n += int(mi) + p.a*10 + arr[1] + len(m) + <-ch + **pp
	if a.(myInt) == 5 && e == nil && f(3) == 6 && st.b == 4 && fl == 4 && i8 == 44 && u8 == 255 && rn == 'A' && nm.name() == "cat" {
		n += 10000000
	}
	return n // 10000000 + 3000000 + 200000 + 30000 + 3000 + 100 + 5+10+8+1+9+4 = 13233137
}

func main() { println("parenTypeConversions", parenTypeConversions()) }
