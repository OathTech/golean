// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised call operands,
// builtin operands and the parenthesised builtin callees beyond len/cap (BUG-287's
// neighbours); expected = gc go1.26.5.

package main

func add(a, b int) int { return a + b }

func sum(xs ...int) int {
	n := 0
	for _, x := range xs {
		n += x
	}
	return n
}

func parenCallArgs() int {
	x, y := 1, 2
	xs := []int{3, 4}
	return add((x), (y))*1000 + add(x, (y))*100 + sum((xs)...)*10 + sum((x), (y), (3)) // 3376
}

func parenBuiltinOperands() int {
	s := []int{1, 2, 3}
	d := make([]int, 2)
	m := map[string]int{"a": 1, "b": 2}
	ch := make(chan int, 1)
	n := len((s))*100000 + cap((s))*10000
	s = append((s), (4))
	n += copy((d), (s)) * 1000
	delete((m), ("a"))
	n += len((m)) * 100
	close((ch))
	t := make(([]int), (3))
	n += len(t) * 10
	p := new((int))
	*p = 7
	n += *p
	clear((m))
	n += len(m)
	q := min((3), (1), (2))
	r := max((3), (1))
	return n*10 + q + r - 3 // 3331371 (-> check)
}

func parenBuiltinCallees() int {
	s := []int{1, 2}
	d := make([]int, 2)
	m := map[string]int{"a": 1}
	ch := make(chan int, 1)
	s = (append)(s, 3)
	n := len(s) * 100000
	n += (copy)(d, s) * 10000
	(delete)(m, "a")
	n += (len)(m) * 1000
	(close)(ch)
	_, ok := <-ch
	if !ok {
		n += 100
	}
	p := (new)(int)
	*p = 4
	n += *p * 10
	t := (make)([]int, 2)
	n += (cap)(t)
	(clear)(d)
	n += d[0]
	return n + (min)(3, 1, 2) + (max)(1, 2) // 310145
}

func parenPrintPanicCallees() int {
	got := 0
	func() {
		defer func() {
			if r := (recover)(); r != nil {
				got = r.(int)
			}
		}()
		(println)("paren-println")
		(print)("paren-print\n")
		(panic)(9)
	}()
	return got // 9, output two lines
}

func main() {
	println("parenCallArgs", parenCallArgs())
	println("parenBuiltinOperands", parenBuiltinOperands())
	println("parenBuiltinCallees", parenBuiltinCallees())
	println("parenPrintPanicCallees", parenPrintPanicCallees())
}
