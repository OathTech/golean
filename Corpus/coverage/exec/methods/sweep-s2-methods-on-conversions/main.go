package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The METHOD RECEIVER route: a value method called directly on the conversion
// expression at every defined kind — int, float, string, bool (the emitter's
// stripped node), and the composites (byte slice, int slice, map, func, chan).

type counter uint64

func (c counter) next() counter { return c + 1 }

type Celsius float64

func (c Celsius) Hot() bool { return c > 30 }

type MyStr string

func (s MyStr) Len() int { return len(s) }

type MyBool bool

func (b MyBool) String() string {
	if b {
		return "yes"
	}
	return "no"
}

type Bytes []byte

func (b Bytes) Len() int { return len(b) }

type MyInts []int

func (s MyInts) Sum() int {
	t := 0
	for _, v := range s {
		t += v
	}
	return t
}

type MyMap map[string]int

func (m MyMap) Get(k string) int { return m[k] }

type MyFn func() int

func (f MyFn) Call() int { return f() + 1 }

type MyChan chan int

func (c MyChan) Send(v int) { c <- v }

func intMethodOnConversion() int {
	var x uint64 = 41
	return int(counter(x).next())
}

func floatMethodOnConversion() (bool, bool) {
	f := 35.5
	return Celsius(f).Hot(), Celsius(f - 10).Hot()
}

func stringMethodOnConversion() int {
	s := "abcd"
	return MyStr(s).Len()
}

func boolMethodOnConversion() string {
	b := true
	return MyBool(b).String() + MyBool(!b).String()
}

func compositeMethodsOnConversion() int {
	s := "abc"
	xs := []int{1, 2, 3}
	m := map[string]int{"k": 4}
	f := func() int { return 5 }
	ch := make(chan int, 1)
	MyChan(ch).Send(7)
	return Bytes(s).Len()*10000 + MyInts(xs).Sum()*1000 + MyMap(m).Get("k")*100 + MyFn(f).Call()*10 + (<-ch - 6)
}

func main() {}
