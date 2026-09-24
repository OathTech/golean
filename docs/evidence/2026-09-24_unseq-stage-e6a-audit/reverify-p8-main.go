package main

// Re-verification probes — the scope-exact R1 environment (fix round 973119c2): declaration forms a
// scope-exact environment might miss (a missed form REFUSES a legal wire), and the shapes whose forgeries
// must now refuse (use-before-declare, a clause binder after its switch, an if-init var after the if).

func wit(x int) int { println("wit", x); return x }

type T struct{ n int }

func (t *T) Bump() int { t.n++; return t.n }

func seq(yield func(int) bool) {
	for i := 0; i < 2; i++ {
		if !yield(i) {
			return
		}
	}
}

func qLabelledLoop() int {
	s := []int{7, 8}
	r := 0
L:
	for i := 0; i < 2; i++ {
		r += s[i] + wit(1)
		if r > 100 {
			break L
		}
		continue L
	}
	return r
}

func qLabelledBlock() int {
	s := []int{7}
	r := 0
	goto L
L:
	{
		i := 0
		r = s[i] + wit(1)
	}
	return r
}

func qSwitchInit() int {
	s := []int{7}
	r := 0
	switch v := wit(0); v {
	case 0:
		r = s[v] + wit(1)
	default:
		r = -1
	}
	return r
}

func qTypeSwitchInit() int {
	s := []int{7}
	r := 0
	var iv interface{} = 0
	switch x := iv; v := x.(type) {
	case int:
		r = s[v] + wit(1)
	case string:
		r = len(v)
	}
	return r
}

func qSwitchCaseDecl() int {
	s := []int{7}
	r := 0
	switch wit(0) {
	case 0:
		i := 0
		r = s[i] + wit(1)
	}
	return r
}

func qRangeFunc() int {
	s := []int{7, 8}
	r := 0
	for v := range seq {
		r += s[v] + wit(1)
	}
	return r
}

func qRangeShadow() int {
	xs := []int{0, 0}
	s := []int{7}
	r := 0
	for _, x := range xs {
		x := x * 2
		r += s[x] + wit(1)
	}
	return r
}

func qOuterAfterInner() int { // the outer int x is visible again after the inner block's string x
	x := 0
	s := []int{7}
	{
		x := "ab"
		_ = x
	}
	return s[x] + wit(1)
}

func qTwoBlocks() int { // two sibling blocks declaring x with different types
	s := []int{7}
	r := 0
	{
		x := "ab"
		r += int(x[1]) + wit(1)
	}
	{
		x := 0
		r += s[x] + wit(2)
	}
	return r
}

func qElseIfInit() int {
	s := []int{7}
	if v := wit(1); v < 0 {
		return -1
	} else if w := wit(0); w >= 0 {
		return s[w] + wit(2)
	}
	return 0
}

func qIfInitInElse() int { // an if-init var referenced in the ELSE branch
	s := []int{7}
	if v := wit(0); v > 0 {
		return -1
	} else {
		return s[v] + wit(1)
	}
}

func qClosureParamShadow() int { // the lifted body's param x (int) vs the enclosing block's x (string)
	x := "ab"
	s := []int{7}
	f := func(x int) int { return s[x] + wit(1) }
	return f(0) + len(x)
}

func qCapturedInLifted() int { // the lifted body reads captured s and i through its $cap params beside a call
	s := []int{7}
	i := 0
	g := func() int { i++; return s[i-1] + wit(1) }
	return g()
}

func qNamedResultAfterBlock() (r int) {
	s := []int{7}
	{
		r := "x"
		_ = r
	}
	r = s[0] + wit(1)
	return
}

func qMethodRecv() int {
	t := &T{}
	return t.Bump() + t.n
}

func qSelectSendRecv() int {
	ch := make(chan int, 1)
	out := make(chan int, 1)
	ch <- 0
	s := []int{7}
	r := 0
	select {
	case out <- wit(0):
		r = -1
	case v := <-ch:
		r = s[v] + wit(1)
	}
	return r
}

func qVarInCase() int {
	s := []int{7}
	r := 0
	switch wit(0) {
	case 0:
		var i int
		r = s[i] + wit(1)
	}
	return r
}

func qDeferLifted() (r int) {
	s := []int{7}
	i := 0
	defer func() { r = s[i] + wit(1) }()
	return 0
}

func qForPostVar() int {
	s := []int{7, 8}
	r := 0
	for i, j := 0, 1; i < 2; i, j = i+1, j+1 {
		r += s[i] + wit(j)
	}
	return r
}

// for the scoping-hole mutants: a graph AFTER a type switch / an if with init / an inner block / a range
func qAfterConstructs() int {
	s := []int{7}
	r := 0
	var iv interface{} = 0
	switch v := iv.(type) {
	case int:
		r = v
	}
	if w := wit(0); w > 5 {
		r = w
	}
	{
		z := "ab"
		_ = z
	}
	for _, k := range s {
		r += k
	}
	return s[r-7] + wit(1)
}

func main() {}

// shadow RESOLUTION order: the innermost declaration must win; a define that redeclares its own operand's name
func qShadowByDefine() int {
	s := []int{7}
	r := 0
	{
		s := s[0] + wit(1) // the graph reads the OUTER []int s; the completion declares the inner int s
		r = s
	}
	return r
}

func qRangeShadowType() int {
	x := "ab"
	s := []int{7, 8}
	r := 0
	for x := range 2 { // the range's int x shadows the string x
		r += s[x] + wit(1)
	}
	return r + len(x)
}

func qForInitShadowType() int {
	i := "ab"
	s := []int{7}
	r := 0
	for i := 0; i < 1; i++ {
		r += s[i] + wit(1)
	}
	return r + len(i)
}

func qIfInitShadowType() int {
	v := "ab"
	s := []int{7}
	if v := wit(0); v >= 0 {
		return s[v] + wit(1)
	}
	return len(v)
}

func qSelectBinderShadowType() int {
	v := "ab"
	ch := make(chan int, 1)
	ch <- 0
	s := []int{7}
	r := 0
	select {
	case v := <-ch:
		r = s[v] + wit(1)
	}
	return r + len(v)
}

// the RANGE-VARIABLE LEAK probe: an outer string k, a range loop declaring its own int k, then a graph using the OUTER k
func qRangeLeakOuter() int {
	k := "ab"
	s := []int{7, 8}
	r := 0
	for _, k := range s {
		r += k
	}
	return s[len(k)-2] + wit(1) + r
}

// the same with a key variable only, and with the for-init spelling (control: for-init declarations are scoped)
func qRangeKeyLeakOuter() int {
	i := "ab"
	s := []int{7, 8}
	r := 0
	for i := range s {
		r += i
	}
	return s[len(i)-2] + wit(1) + r
}

func qForInitNoLeak() int {
	i := "ab"
	s := []int{7, 8}
	r := 0
	for i := 0; i < 2; i++ {
		r += i
	}
	return s[len(i)-2] + wit(1) + r
}

// a graph after a select whose clause bound the only `v`: a forged reference to v after the select must refuse
func qAfterSelect() int {
	ch := make(chan int, 1)
	ch <- 0
	s := []int{7}
	r := 0
	select {
	case v := <-ch:
		r = v
	}
	return s[r] + wit(1)
}
