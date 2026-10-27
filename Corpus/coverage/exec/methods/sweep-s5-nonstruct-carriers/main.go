package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// NON-STRUCT carriers (defined int, slice, map, func, chan, array, string, bool,
// float) across the dynamic routes: interface dispatch from value and pointer
// boxes (a value method dispatched on a `*MyInt` box reads the pointee — a
// non-struct cell, so the receiver retag is a no-op), a pointer method
// mutating through the box, satisfaction, auto-address, method values and
// expressions, and a type switch over value vs pointer boxes.

type MyInt int

func (m MyInt) Double() int { return int(m) * 2 }
func (m *MyInt) Inc()       { *m++ }

type Doubler interface{ Double() int }
type Incer interface{ Inc() }

func intDispatch() int {
	var d Doubler = MyInt(3)
	v := MyInt(4)
	var pd Doubler = &v // *MyInt ⊇ MyInt's value methods: deref on a non-struct pointee
	v = 10              // the box holds the pointer: the dispatch reads the live cell
	return d.Double()*100 + pd.Double()
}

func intPointerMethodBox() int {
	v := MyInt(5)
	var i Incer = &v
	i.Inc()
	i.Inc()
	var a any = v
	_, okVal := a.(Incer) // the value box lacks the pointer method
	var b any = &v
	_, okPtr := b.(Incer)
	r := int(v) * 100
	if okVal {
		r += 10
	}
	if okPtr {
		r += 1
	}
	return r
}

type MySlice []int

func (s MySlice) Sum() int {
	t := 0
	for _, x := range s {
		t += x
	}
	return t
}

type MyMap map[string]int

func (m MyMap) Sum() int {
	t := 0
	for _, x := range m {
		t += x
	}
	return t
}

type Summer interface{ Sum() int }

func sliceMapDispatch() int {
	var a Summer = MySlice{1, 2, 3}
	var b Summer = MyMap{"x": 10, "y": 20}
	var c any = MySlice(nil)
	_, okSlice := c.(Summer)
	var d any = []int{1}
	_, okPlain := d.(Summer) // the unnamed slice carries no methods
	r := a.Sum()*1000 + b.Sum()
	if okSlice {
		r += 100000
	}
	if okPlain {
		r += 1000000
	}
	return r
}

type MyFn func(int) int

func (f MyFn) Apply(x int) int { return f(x) + 1 }

type MyChan chan int

func (c MyChan) Put(v int) int {
	c <- v
	return len(c)
}

type Applier interface{ Apply(int) int }
type Putter interface{ Put(int) int }

func funcChanDispatch() int {
	var a Applier = MyFn(func(x int) int { return x * 3 })
	ch := make(MyChan, 2)
	var p Putter = ch
	n := p.Put(7)
	var x any = ch
	_, okChan := x.(Putter)
	_, okApplyOnChan := x.(Applier)
	r := a.Apply(4)*100 + n*10 + <-ch
	if okChan {
		r += 1000
	}
	if okApplyOnChan {
		r += 10000
	}
	return r
}

type MyArr [3]int
type MyStr string
type MyBool bool
type MyFloat float64

func (a MyArr) First() int   { return a[0] }
func (s MyStr) First() int   { return int(s[0]) }
func (f MyFloat) First() int { return int(f) }
func (b MyBool) First() int {
	if b {
		return 1
	}
	return 0
}

type Firster interface{ First() int }

func arrayStringBoolFloatDispatch() int {
	boxes := []Firster{MyArr{7, 8, 9}, MyStr("A"), MyBool(true), MyFloat(2.75)}
	r := 0
	for _, b := range boxes {
		r = r*100 + b.First()
	}
	var x any = MyArr{1, 2, 3}
	if _, ok := x.(Firster); ok {
		r++
	}
	var y any = [3]int{1, 2, 3}
	if _, ok := y.(Firster); ok {
		r += 1000000
	}
	return r
}

func nonstructAutoAddress() int {
	var m MyInt = 1
	m.Inc() // (&m).Inc()
	xs := []MyInt{10, 20}
	xs[1].Inc()
	arr := [2]MyInt{30, 40}
	arr[0].Inc()
	pm := &m
	pm.Inc() // already a pointer: used as is
	return int(m)*10000 + int(xs[1])*100 + int(arr[0])
}

func nonstructMethodValues() int {
	var m MyInt = 2
	f := m.Double // the receiver copied at bind time
	g := m.Inc    // the address captured
	m = 7
	g()
	return f()*100 + int(m)
}

func nonstructMethodExpressions() int {
	var m MyInt = 3
	d := MyInt.Double
	i := (*MyInt).Inc
	i(&m)
	return d(m)*100 + int(m)
}

func nonstructTypeSwitch() int {
	v := MyInt(1)
	classify := func(x any) int {
		switch x.(type) {
		case Incer:
			return 1
		case Doubler:
			return 2
		default:
			return 3
		}
	}
	return classify(v)*100 + classify(&v)*10 + classify(int(v))
}

func main() {
	intDispatch()
	intPointerMethodBox()
	sliceMapDispatch()
	funcChanDispatch()
	arrayStringBoolFloatDispatch()
	nonstructAutoAddress()
	nonstructMethodValues()
	nonstructMethodExpressions()
	nonstructTypeSwitch()
}
