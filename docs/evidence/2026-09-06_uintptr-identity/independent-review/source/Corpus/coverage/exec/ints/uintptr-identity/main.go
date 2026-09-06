// BUG-107: uintptr and uint64 have distinct Go type identities even on
// the pinned 64-bit target. Equal storage widths do not identify types.
package main

type PointerMethod struct{}

func (PointerMethod) M(x uintptr) {}

type UintMethod interface{ M(uint64) }
type PointerRequirement interface{ M(uintptr) }

type PointerResult struct{}

func (PointerResult) M() uintptr { return 7 }

type UintResult interface{ M() uint64 }

func assertions() int {
	out := 0
	var a any = uintptr(7)
	if _, ok := a.(uint64); ok {
		out += 1
	}
	var b any = uint64(7)
	if _, ok := b.(uintptr); ok {
		out += 2
	}
	if _, ok := a.(uintptr); ok {
		out += 8
	}
	return out
}

func methodParameters() int {
	out := 0
	var v any = PointerMethod{}
	if _, ok := v.(UintMethod); ok {
		out += 1
	}
	if _, ok := v.(PointerRequirement); ok {
		out += 8
	}
	return out
}

func methodResults() bool {
	var v any = PointerResult{}
	_, ok := v.(UintResult)
	return ok
}

func aggregateIdentity() int {
	out := 0
	var a any = [1]uintptr{7}
	if _, ok := a.([1]uint64); ok {
		out += 1
	}
	var p any = new(uintptr)
	if _, ok := p.(*uint64); ok {
		out += 2
	}
	var s any = []uintptr{7}
	if _, ok := s.([]uint64); ok {
		out += 4
	}
	return out
}

func mapKeys() int {
	m := make(map[any]int)
	m[uintptr(7)] = 11
	m[uint64(7)] = 22
	return len(m)*100 + m[uintptr(7)] + m[uint64(7)]
}

func wrap() bool {
	x := ^uintptr(0)
	return x+1 == 0 && x>>63 == 1 && uintptr(uint64(x)) == x
}

func directReadout() uintptr { return 7 }

func boxedReadout() any { return uintptr(7) }

func main() {
	println(assertions(), methodParameters(), methodResults(), aggregateIdentity(), mapKeys(), wrap())
}
