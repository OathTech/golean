// noodler probes — assorted statement and type shapes (spec#For_range
// over integers/channels without variables, spec#Goto_statements,
// spec#Labeled_statements, spec#Function_types, spec#Struct_types).
package main

// for range n with no variable (Go 1.22).
func rangeIntNoVar() int {
	count := 0
	for range 4 {
		count++
	}
	s := "abc"
	for range len(s) {
		count += 10
	}
	return count
}

// for range over a channel with no variable.
func rangeChanNoVar() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	close(ch)
	n := 0
	for range ch {
		n++
	}
	return n
}

// goto forward out of a nested if into a label followed by a loop.
func gotoForwardOutOfNestedIf(x int) int {
	r := 0
	if x > 0 {
		if x > 5 {
			goto big
		}
		r = 1
	}
	r += 10
	return r
big:
	for i := 0; i < 3; i++ {
		r += 100
	}
	return r
}

// Labeled continue inside nested range over a single-key map and slice.
func labeledContinueNested() int {
	m := map[string][]int{"k": {1, 2, 3, 4}}
	total := 0
outer:
	for _, vs := range m {
		for _, v := range vs {
			if v == 3 {
				continue outer
			}
			total += v
		}
		total += 1000
	}
	return total
}

// Function returning a function returning a function.
func curriedAdd() int {
	add := func(a int) func(int) func(int) int {
		return func(b int) func(int) int {
			return func(c int) int { return a + b + c }
		}
	}
	return add(1)(2)(3) * add(10)(0)(0)
}

// Array of channels.
func arrayOfChannels() int {
	var chs [3]chan int
	for i := range chs {
		chs[i] = make(chan int, 1)
		chs[i] <- i * 2
	}
	return <-chs[0] + <-chs[1] + <-chs[2]
}

// Conversion between named func types.
type F func(int) int
type G func(int) int

func convertNamedFuncTypes() int {
	f := F(func(x int) int { return x + 1 })
	g := G(f)
	var h func(int) int = g
	return h(1) + g(2) + f(3)
}

// Struct embedding an interface AND defining the same method: the outer
// method wins; the embedded one is reachable by explicit path.
type Namer interface{ Name() string }
type plain struct{}

func (plain) Name() string { return "plain" }

type Wrapped struct{ Namer }

func (Wrapped) Name() string { return "wrapped" }

func embeddedInterfaceShadowed() string {
	w := Wrapped{plain{}}
	var n Namer = w
	return n.Name() + "/" + w.Namer.Name()
}

// switch with init and no tag.
func switchInitNoTag(x int) int {
	switch y := x * 3; {
	case y > 10:
		return 1
	case y > 5:
		return 2
	default:
		return 3
	}
}

// Recursive struct through a slice: count nodes.
type tree struct {
	kids []tree
}

func recursiveSliceStruct() int {
	t := tree{kids: []tree{{}, {kids: []tree{{}, {}}}}}
	var count func(tree) int
	count = func(t tree) int {
		n := 1
		for _, k := range t.kids {
			n += count(k)
		}
		return n
	}
	return count(t)
}

// Unary plus, and repeated unary minus.
func unaryOperators() (int, int, float64) {
	x := 5
	y := -(-x)
	return +x, -y, -(-2.5)
}

// Iota-based flag masks with bit-clear.
type Perm uint8

const (
	Read Perm = 1 << iota
	Write
	Exec
)

func iotaFlagMasks() (Perm, bool, Perm) {
	p := Read | Exec
	p |= Write
	p &^= Read
	return p, p&Exec != 0, ^p & (Read | Write | Exec)
}

// copy into an array's slice view.
func copyIntoArrayView() int {
	var a [4]int
	n := copy(a[1:], []int{7, 8, 9, 10})
	return n*1000 + a[0]*100 + a[1]*10 + a[3]
}

// Indexed array literal with a gap: len is max index + 1.
func indexedArrayLiteral() (int, int, int) {
	x := [...]int{5: 1, 2: 3}
	return len(x), x[2], x[4]
}

// switch true with boolean cases.
func switchTrueTag(x int) int {
	switch true {
	case x < 0:
		return -1
	case x == 0:
		return 0
	}
	return 1
}

// else-if chain with init scoping.
func elseIfChain(x int) int {
	if v := x * 2; v > 10 {
		return v
	} else if w := v + 1; w > 5 {
		return w
	} else {
		return v + w
	}
}

// A method on a pointer to a local struct acting as a counter.
type ctr struct{ n int }

func (c *ctr) bump() int { c.n++; return c.n }

func pointerMethodCounter() int {
	c := &ctr{}
	c.bump()
	c.bump()
	return c.bump()
}

// Shadowed package-level variable inside a function, then package value
// unchanged.
var shadowMe = 1

func shadowPackageVar() (int, int) {
	shadowMe := 2
	shadowMe++
	return shadowMe, packageShadowMe()
}

func packageShadowMe() int { return shadowMe }

// Slice of slices with shared inner backing.
func sliceOfSlicesSharing() int {
	inner := []int{1, 2, 3}
	ss := [][]int{inner, inner[1:]}
	ss[1][0] = 20
	return ss[0][1] + inner[1]
}

// Struct value in an array modified through index.
func structInArrayModify() int {
	type P struct{ x int }
	arr := [2]P{}
	arr[1].x = 5
	arr[0].x += arr[1].x
	return arr[0].x*10 + arr[1].x
}

// Complex control: break out of a select inside a switch inside a loop
// with labels.
func labeledBreakThroughSwitchSelect() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	n := 0
loop:
	for {
		switch {
		default:
			select {
			case v := <-ch:
				n += v
				if v == 2 {
					break loop
				}
			}
		}
	}
	return n
}

func main() {}
