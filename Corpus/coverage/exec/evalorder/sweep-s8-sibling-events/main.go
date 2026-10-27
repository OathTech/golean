package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27): the sibling EVENT is not a plain function
// call — a pointer-receiver method call, an interface method call, a generic call, a method
// value / method expression / promoted method call, a receive (witnessed by len(ch) after
// recovery), a panicking call (panic identity), an immediately-invoked func literal —
// beside a non-call operand it mutates or races against in panic identity. Membership
// rows where the grammar admits the sweep; strict rows where the legacy call-first order
// is gc's. The assertion beside an INTERFACE method call is BUG-310's row
// (sweep-s8-early-kinds-legacy/event-iface-method-call-assertion).

type O struct {
	px  *int
	pi  *int
	pp  **int
	piv *any
	ps  *string
}

func (o *O) SetPX() int           { *o.px = 5; return 10 }
func (o *O) SetPI() int           { *o.pi = 1; return 10 }
func (o *O) Redirect(y *int) int  { *o.pp = y; return 10 }
func (o *O) SetIv() int           { *o.piv = 5; return 10 }
func (o *O) SetS() int            { *o.ps = "zz"; return 1 }

type Setter interface {
	SetPX() int
	SetIv() int
}

type Outer struct{ O }

func setG[T any](p *T, v T) int { *p = v; return 10 }

func boom() int { panic("boom") }

// --- a pointer-receiver method call as the event ---

func methodCallLocalVar() int {
	x := 1
	o := &O{px: &x}
	return x + o.SetPX()
}

func methodCallIndex() int {
	s := []int{1, 5}
	i := 0
	o := &O{pi: &i}
	return s[i] + o.SetPI()
}

func methodCallDeref() int {
	x, y := 1, 5
	p := &x
	o := &O{pp: &p}
	return *p + o.Redirect(&y)
}

func methodCallAssertion() int {
	var iv any = 1
	o := &O{piv: &iv}
	return iv.(int) + o.SetIv()
}

func methodCallBytesConv() int {
	s := "ab"
	o := &O{ps: &s}
	return int([]byte(s)[0]) + o.SetS()
}

// --- an interface method call as the event (legacy: dynamic dispatch has no callee value) ---

func ifaceMethodCallLocalVar() int {
	x := 1
	var i Setter = &O{px: &x}
	return x + i.SetPX()
}

// --- a generic call, a method value, a method expression, a promoted method ---

func genericCallLocalVar() int {
	x := 1
	return x + setG(&x, 5)
}

func methodValueCallLocalVar() int {
	x := 1
	o := &O{px: &x}
	mv := o.SetPX
	return x + mv()
}

func methodExprCallLocalVar() int {
	x := 1
	o := &O{px: &x}
	return x + (*O).SetPX(o)
}

func promotedCallLocalVar() int {
	x := 1
	w := &Outer{O{px: &x}}
	return x + w.SetPX()
}

// --- a receive as the event: the witness is len(ch) after recovery (1 = the operand's
// panic first, 0 = the receive first) ---

func recvVsIndexPanic() (r int) {
	ch := make(chan int, 1)
	ch <- 1
	s := []int{1}
	i := 5
	defer func() { recover(); r = len(ch) }()
	return s[i] + <-ch
}

func recvVsNilDeref() (r int) {
	ch := make(chan int, 1)
	ch <- 1
	var p *int
	defer func() { recover(); r = len(ch) }()
	return *p + <-ch
}

func recvVsStringSlicePanic() (r int) {
	ch := make(chan int, 1)
	ch <- 1
	s := "ab"
	i, j := 5, 7
	defer func() { recover(); r = len(ch) }()
	return int([]byte(s[i:j])[0]) + <-ch
}

// --- a panicking call as the event (panic identity) ---

func panickingCallVsAssertion() int {
	var iv any = "s"
	return iv.(int) + boom()
}

func panickingCallVsNilDeref() int {
	var p *int
	return *p + boom()
}

func panickingCallVsStringSlice() int {
	s := "ab"
	i, j := 5, 7
	return int([]byte(s[i:j])[0]) + boom()
}

// --- an immediately-invoked func literal as the event ---

func invokedLitLocalVar() int {
	x := 1
	return x + func() int { x = 100; return 1 }()
}

func invokedLitIndex() int {
	s := []int{1, 5}
	i := 0
	return s[i] + func() int { i = 1; return 1 }()
}
