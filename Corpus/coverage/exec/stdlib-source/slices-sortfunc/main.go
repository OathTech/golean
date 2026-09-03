package main

// slices through the REAL source-through package (slice 2, 2026-09-03):
// slices.SortFunc is gc's pdqsortCmpFunc stenciled per element type by
// mono.go (the insertion-sort shim RETIRED), so the machine realizes gc's
// exact member — including the tie order the docs leave open ("not
// guaranteed to be stable"). Rows: past the 12-element insertion-sort
// threshold (pdqsort's pivot/partition paths), a reversed input (the
// pattern-breaking path), a NAMED slice type (the old shim's S == []E
// bound — row slices/sortfunc-cmp/named-slice-bound turns green), ties
// PROJECTED (tie-insensitive: the doc contract) and ties REALIZED (the
// exact order — a version-tracked (b)-pin of gc's pdqsort member under
// G4(a); latitude inventory R13 note), plus the other pure members that
// now lower (Index/Contains/Reverse/Max/Min/Equal/Compact/BinarySearch,
// SortStableFunc). slices.Sort itself stays the sortSlice MACHINE OP.

import (
	"cmp"
	"slices"
	"strings"
)

type Ints []int

type kv struct {
	k  int
	id int
}

func lcg(seed, n, mod int) []int {
	xs := make([]int, 0, n)
	x := seed
	for i := 0; i < n; i++ {
		x = (x*1103515245 + 12345) % 2147483648
		xs = append(xs, x%mod)
	}
	return xs
}

func render(xs []int) string {
	var b strings.Builder
	b.Grow(8 * len(xs)) // one spill, so strict rows stay inside the 10-pick invariance streams
	for i, x := range xs {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(itoa(x))
	}
	return b.String()
}

func sortFuncLarge() string {
	xs := lcg(7, 40, 50)
	slices.SortFunc(xs, func(a, b int) int { return cmp.Compare(a, b) })
	return render(xs)
}

func sortFuncReversedInput() string {
	xs := make([]int, 0, 30)
	for i := 30; i > 0; i-- {
		xs = append(xs, i*3)
	}
	slices.SortFunc(xs, func(a, b int) int { return a - b })
	return render(xs)
}

func sortFuncNamedSlice() string {
	xs := Ints{9, 3, 7, 1, 8}
	slices.SortFunc(xs, func(a, b int) int { return cmp.Compare(b, a) })
	return render(xs)
}

func sortFuncStringsByLen() string {
	xs := []string{"ccc", "a", "dddd", "bb", "", "eeeee", "ff"}
	slices.SortFunc(xs, func(a, b string) int { return cmp.Compare(len(a), len(b)) })
	return strings.Join(xs, "|")
}

func tiesInput() []kv {
	ks := lcg(3, 30, 4)
	out := make([]kv, 0, 30)
	for i, k := range ks {
		out = append(out, kv{k, i})
	}
	return out
}

// Tie-insensitive: keys sorted + the multiset of ids per key (sorted).
func sortFuncTiesProjected() string {
	xs := tiesInput()
	slices.SortFunc(xs, func(a, b kv) int { return cmp.Compare(a.k, b.k) })
	var b strings.Builder
	b.Grow(256)
	prev := -1
	group := make([]int, 0, len(xs))
	flush := func() {
		slices.Sort(group)
		b.WriteString(itoa(prev) + ":" + render(group) + ";")
		group = group[:0]
	}
	for _, x := range xs {
		if x.k != prev && prev != -1 {
			flush()
		}
		prev = x.k
		group = append(group, x.id)
	}
	flush()
	return b.String()
}

// The REALIZED tie order: gc's pdqsortCmpFunc member, exactly (a
// version-tracked pin — a toolchain that changes pdqsort moves this row).
func sortFuncTiesRealized() string {
	xs := tiesInput()
	slices.SortFunc(xs, func(a, b kv) int { return cmp.Compare(a.k, b.k) })
	ids := make([]int, 0, len(xs))
	for _, x := range xs {
		ids = append(ids, x.id)
	}
	return render(ids)
}

func sortStableFunc() string {
	xs := tiesInput()
	slices.SortStableFunc(xs, func(a, b kv) int { return cmp.Compare(a.k, b.k) })
	ids := make([]int, 0, len(xs))
	for _, x := range xs {
		ids = append(ids, x.id)
	}
	return render(ids)
}

func slicesOthers() string {
	xs := []int{4, 1, 4, 4, 9, 2, 2}
	i := slices.Index(xs, 9)
	c := slices.Contains(xs, 7)
	mx, mn := slices.Max(xs), slices.Min(xs)
	ys := slices.Clone(xs)
	slices.Reverse(ys)
	eq := slices.Equal(xs, ys)
	zs := slices.Compact(slices.Clone(xs))
	sorted := []int{1, 3, 5, 7}
	pos, found := slices.BinarySearch(sorted, 5)
	pos2, found2 := slices.BinarySearch(sorted, 4)
	return itoa(i) + " " + boolStr(c) + " " + itoa(mx) + " " + itoa(mn) + " " + render(ys) + " " + boolStr(eq) + " " + render(zs) + " " + itoa(pos) + boolStr(found) + " " + itoa(pos2) + boolStr(found2)
}

func boolStr(b bool) string {
	if b {
		return "T"
	}
	return "F"
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	neg := n < 0
	if neg {
		n = -n
	}
	out := ""
	for n > 0 {
		out = string(rune('0'+n%10)) + out
		n /= 10
	}
	if neg {
		return "-" + out
	}
	return out
}

func main() {
	println(sortFuncLarge())
	println(sortFuncReversedInput())
	println(sortFuncNamedSlice())
	println(sortFuncStringsByLen())
	println(sortFuncTiesProjected())
	println(sortFuncTiesRealized())
	println(sortStableFunc())
	println(slicesOthers())
}
