package main

// S14 sweep (lane sweep/s14-map-iter, 2026-10-27; members BUG-005, BUG-088):
// the ROUTES by which a range body reaches the ranged map — nested ranges
// over the same map, calls, aliases, struct-field and map-element paths,
// loop exits (break / continue / return / goto / labelled break / panic),
// deferred literals, maps of maps, re-assignment of the ranged variable, the
// four binding forms, a bounded self-inserting loop, gc's small-group growth,
// a call-result operand, read-modify-write, the generic and method routes,
// closures over the key, a second range after the mutation. Observations are
// order-independent (counts, sums, lengths); -1 is the runaway guard.

// nested-delete-outer-current: the inner range over the same map deletes the
// outer's current key at every inner production. Outer 3; the inner may
// produce k before deleting it (3) or not (2), then 2 or 1, then 1: inner
// total 4..6 -> {340, 350, 360}.
func s14NestedDeleteOuterCurrent() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	outer, inner := 0, 0
	for k := range m {
		outer++
		if outer > 8 {
			return -1
		}
		for range m {
			inner++
			if inner > 30 {
				return -2
			}
			delete(m, k)
		}
	}
	return outer*100 + inner*10 + len(m)
}

// nested-delete-others: the inner range deletes every key but the outer's
// current: the outer never reaches them (1 outer production, 3 inner, len 1).
func s14NestedDeleteOthers() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	outer, inner := 0, 0
	for k := range m {
		outer++
		if outer > 8 {
			return -1
		}
		for j := range m {
			inner++
			if inner > 30 {
				return -2
			}
			if j != k {
				delete(m, j)
			}
		}
	}
	return outer*100 + inner*10 + len(m)
}

// nested-insert: the inner range inserts key 11 whenever it ranges key 1; the
// outer may produce 11 or not; the first inner may produce it or not, the
// later inners always do: {250, 260, 381, 391}.
func s14NestedInsert() int {
	m := map[int]int{1: 1, 2: 2}
	outer, inner, c11 := 0, 0, 0
	for k := range m {
		outer++
		if outer > 8 {
			return -1
		}
		if k == 11 {
			c11++
		}
		for j := range m {
			inner++
			if inner > 30 {
				return -2
			}
			if j == 1 {
				m[11] = 11
			}
		}
	}
	return outer*100 + inner*10 + c11
}

func delKey(m map[int]int, k int) { delete(m, k) }
func insKey(m map[int]int, k int) { m[k] = k }

// delete-via-call: the current key deleted through a function call.
func s14DeleteViaCall() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		delKey(m, k)
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// insert-via-call: a key created through a function call at the first
// production. Strict cut: start keys once each, the created at most once.
func s14InsertViaCall() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			insKey(m, 4)
		}
	}
	if c[4] > 1 {
		return -5
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// via-alias: another variable holding the same map deletes the current key
// and inserts one (deleted in turn if produced). Strict cut: start keys once,
// the created at most once, len + its count = 1.
func s14ViaAlias() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	m2 := m
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		delete(m2, k)
		if n == 1 {
			m2[4] = 4
		}
	}
	if c[4] > 1 {
		return -5
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + (len(m) + c[4])
}

type holder struct{ m map[int]int }

// via-paths: the map reached through a struct field and through a map
// element, the current key deleted through the same path, one insert.
func s14ViaPaths() int {
	s := holder{m: map[int]int{1: 1, 2: 2, 3: 3}}
	mm := map[string]map[int]int{"x": {1: 1, 2: 2, 3: 3}}
	c := map[int]int{}
	n := 0
	for k := range s.m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		delete(s.m, k)
	}
	d := map[int]int{}
	for k := range mm["x"] {
		n++
		if n > 16 {
			return -1
		}
		d[k]++
		delete(mm["x"], k)
		if n == 4 {
			mm["x"][4] = 4
		}
	}
	if d[4] > 1 {
		return -5
	}
	return (c[1]*1000+c[2]*100+c[3]*10+len(s.m))*10000 + d[1]*1000 + d[2]*100 + d[3]*10 + (len(mm["x"]) + d[4])
}

// break-after-delete: break at the first production after deleting an
// unreached key.
func s14BreakAfterDelete() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		delete(m, k%3+1)
		break
	}
	return n*10 + len(m)
}

// continue-after-mutation: continue after deleting the current key 1 and
// inserting 4 (which deletes itself if produced). Strict cut.
func s14ContinueAfterMutation() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if k == 1 {
			delete(m, 1)
			m[4] = 4
			continue
		}
		if k == 4 {
			delete(m, 4)
		}
	}
	if c[4] > 1 {
		return -5
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + (len(m) - 2 + c[4])
}

func helperReturnMid(m map[int]int) int {
	for k := range m {
		delete(m, k)
		return k
	}
	return 0
}

// return-mid: return from inside the loop after a delete (observed through len).
func s14ReturnMid() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	k0 := helperReturnMid(m)
	r := len(m) * 10
	if k0 > 0 {
		r++
	}
	return r
}

// goto-out: goto out of the loop at the second production after a
// delete-current + insert at each.
func s14GotoOut() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		delete(m, k)
		m[k+10] = k
		if n == 2 {
			goto done
		}
	}
done:
	return n*100 + len(m)*10
}

// defer-literal-mutates-mid: a deferred func literal deletes the next key
// when its enclosing literal returns, mid-iteration (`defer delete(...)` of
// the builtin itself is frontend-quarantined — a named refusal, not rowed).
// Admitted set {111, 1011, 1101}: two productions, the deleted next key never.
func s14DeferLiteralMutatesMid() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		func() {
			defer func() { delete(m, k%3+1) }()
		}()
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// defer-literal-inserts-mid: a deferred literal inserts at the first
// production. Strict cut.
func s14DeferLiteralInsertsMid() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			func() {
				defer func() { m[4] = 4 }()
			}()
		}
	}
	if c[4] > 1 {
		return -5
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// defer-after-range: a defer of the enclosing function mutates after the
// range ended (named result).
func s14DeferAfterRange() (r int) {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	defer func() {
		delete(m, 1)
		r = r*10 + len(m)
	}()
	n := 0
	for range m {
		n++
	}
	return n
}

// outer-range-inner-mutate: a map of maps — range the outer, mutate the
// inner maps.
func s14OuterRangeInnerMutate() int {
	mm := map[int]map[int]int{1: {1: 1}, 2: {2: 2}}
	n := 0
	for k, inner := range mm {
		n++
		if n > 8 {
			return -1
		}
		delete(inner, k)
		inner[k+10] = k
		inner[k+20] = k
	}
	return n*100 + len(mm[1])*10 + len(mm[2])
}

// range-inner-delete-from-outer: range an inner map while deleting it from
// the outer; the ranged object lives on.
func s14RangeInnerDeleteFromOuter() int {
	mm := map[int]map[int]int{1: {1: 1, 2: 2, 3: 3}}
	n := 0
	for range mm[1] {
		n++
		if n > 8 {
			return -1
		}
		delete(mm, 1)
	}
	return n*10 + len(mm)
}

// reassign-variable: the ranged VARIABLE re-assigned mid-iteration — the
// range expression was evaluated once; the original map is iterated.
func s14ReassignVariable() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	other := map[int]int{7: 7}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		m = other
		m[8] = 8
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// len-during-delete: len read at every production while deleting the current.
func s14LenDuringDelete() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, n := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += len(m)
		delete(m, k)
	}
	return sum*10 + n
}

// comma-ok-during-delete: comma-ok lookups of the deleted key 1 (never ok
// after the first production) and of the current key (ok unless it is 1,
// just deleted) at every production: exactly two ok lookups either way.
func s14CommaOkDuringDelete() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n, okc := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		delete(m, 1)
		if _, ok := m[1]; ok {
			okc++
		}
		if _, ok := m[k]; ok {
			okc += 10
		}
	}
	if okc != 20 || n < 2 || n > 3 {
		return -5
	}
	return len(m)*10 + 1
}

// bare-form: `for range m` deleting key n at the n-th production — the
// deleted key is the current (n=3, len 0) or an unreached one (n=2, len 1):
// {21, 30}.
func s14BareForm() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for range m {
		n++
		if n > 8 {
			return -1
		}
		delete(m, n)
	}
	return n*10 + len(m)
}

// key-value-form: `for k, v := range m` deleting the current key.
func s14KeyValueForm() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, n := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
	}
	return sum*10 + len(m)
}

// value-only-form: `for _, v := range m` deleting key v.
func s14ValueOnlyForm() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, n := 0, 0
	for _, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, v)
	}
	return sum*10 + len(m)
}

// assign-form: `for k, v = range m` into pre-declared variables, deleting
// the current key; the variables keep the last production.
func s14AssignForm() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	var k, v int
	sum, n := 0, 0
	for k, v = range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
	}
	r := sum*100 + len(m)
	if k == v {
		r += 10
	}
	return r
}

// self-insert-bounded: each production of k < 40 inserts k+10; the chain
// 1 -> 11 -> 21 -> 31 -> 41 may stop at any created entry: {12, 23, 34, 45, 55}.
func s14SelfInsertBounded() int {
	m := map[int]int{1: 1}
	n := 0
	for k := range m {
		n++
		if n > 20 {
			return -1
		}
		if k < 40 {
			m[k+10] = k
		}
	}
	return n*10 + len(m)
}

// growth-delete-unreached: six inserts at the first production push the map
// past gc's 8-slot small group (growth mid-iteration) while an unreached
// start key is deleted; strict cut: exactly two start keys produced, no
// created entry twice, at most six created produced, len 8.
func s14GrowthDeleteUnreached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n, start, fresh := 0, 0, 0
	for k := range m {
		n++
		if n > 12 {
			return -1
		}
		c[k]++
		if k >= 10 {
			fresh++
			if c[k] > 1 {
				return -3
			}
		} else {
			start++
			if c[k] > 1 {
				return -2
			}
		}
		if n == 1 {
			delete(m, k%3+1)
			for i := 10; i < 16; i++ {
				m[i] = i
			}
		}
	}
	if fresh > 6 {
		return -4
	}
	return start*100 + len(m)
}

// range-call-result: the range operand is a call returning the map; the body
// mutates the same object through the closure's variable.
func s14RangeCallResult() int {
	g := map[int]int{1: 1, 2: 2, 3: 3}
	get := func() map[int]int { return g }
	c := map[int]int{}
	n := 0
	for k := range get() {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		delete(g, k)
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(g)
}

// read-modify-write-current: `m[k]++` and `m[k] += 10` on the current key.
func s14ReadModifyWriteCurrent() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		m[k]++
		m[k] += 10
	}
	return m[1] + m[2] + m[3]
}

type pt struct{ a, b int }

func delAll[K comparable, V any](m map[K]V) int {
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		delete(m, k)
	}
	return n
}

// generic-route: a type-parameterised function deletes the current key.
func s14GenericRoute() int {
	m := map[string]pt{"a": {1, 1}, "b": {2, 2}, "c": {3, 3}}
	n := delAll(m)
	return n*10 + len(m)
}

type mm map[int]int

func (m mm) drop(k int) { delete(m, k) }
func (m mm) put(k int)  { m[k] = k }

// defined-map-methods: a defined map type mutated through its methods.
// Strict cut: start keys once, the created at most once.
func s14DefinedMapMethods() int {
	m := mm{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		m.drop(k)
		if n == 1 {
			m.put(4)
		}
	}
	if c[4] > 1 {
		return -5
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + (len(m) + c[4])
}

func rangePanics(m map[int]int) (r int) {
	defer func() {
		if recover() != nil {
			r = len(m)
		}
	}()
	for k := range m {
		delete(m, k)
		panic("mid-range")
	}
	return -1
}

// panic-after-delete: a panic after a delete inside the loop, recovered by
// the ranging function's deferred literal; the delete stays.
func s14PanicAfterDelete() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	return rangePanics(m)*10 + len(m)
}

// capture-keys-while-deleting: per-iteration key variables captured by
// closures while the current key is deleted.
func s14CaptureKeysWhileDeleting() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	var fs [3]func() int
	i := 0
	for k := range m {
		fs[i] = func() int { return k }
		i++
		delete(m, k)
	}
	sum := 0
	for _, f := range fs {
		sum += f()
	}
	return sum*10 + len(m)
}

// labelled-break: a labelled break out of the enclosing loop from the inner
// range after a delete of the current key.
func s14LabelledBreak() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
outer:
	for i := 0; i < 10; i++ {
		for k := range m {
			n++
			delete(m, k)
			if n == 2 {
				break outer
			}
		}
	}
	return n*10 + len(m)
}

// second-range-after-mutation: a second range after a first one that
// cleared and re-filled the map sees the live entries.
func s14SecondRangeAfterMutation() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for range m {
		n++
		if n > 8 {
			return -1
		}
		if n == 1 {
			clear(m)
			m[7] = 7
			m[8] = 8
		}
	}
	sum := 0
	for k := range m {
		sum += k
		delete(m, k)
	}
	return sum*10 + len(m)
}

func main() {
	println(s14NestedDeleteOuterCurrent())
	println(s14NestedDeleteOthers())
	println(s14NestedInsert())
	println(s14DeleteViaCall())
	println(s14InsertViaCall())
	println(s14ViaAlias())
	println(s14ViaPaths())
	println(s14BreakAfterDelete())
	println(s14ContinueAfterMutation())
	println(s14ReturnMid())
	println(s14GotoOut())
	println(s14DeferLiteralMutatesMid())
	println(s14DeferLiteralInsertsMid())
	println(s14DeferAfterRange())
	println(s14OuterRangeInnerMutate())
	println(s14RangeInnerDeleteFromOuter())
	println(s14ReassignVariable())
	println(s14LenDuringDelete())
	println(s14CommaOkDuringDelete())
	println(s14BareForm())
	println(s14KeyValueForm())
	println(s14ValueOnlyForm())
	println(s14AssignForm())
	println(s14SelfInsertBounded())
	println(s14GrowthDeleteUnreached())
	println(s14RangeCallResult())
	println(s14ReadModifyWriteCurrent())
	println(s14GenericRoute())
	println(s14DefinedMapMethods())
	println(s14PanicAfterDelete())
	println(s14CaptureKeysWhileDeleting())
	println(s14LabelledBreak())
	println(s14SecondRangeAfterMutation())
}
