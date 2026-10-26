// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K17 type parameters: inside a generic body a `T` value boxed carries the ARGUMENT's identity
// (byte ≡ uint8; int ≢ int64; a local type argument is itself); an assertion to `T` / `[]T`
// inside the body keys on the argument too.

type A = int

func isInt[T any](x T) bool { _, ok := any(x).(int); return ok }

func isT[T any](x any) bool { _, ok := x.(T); return ok }

func sw[T any](x any) int {
	switch x.(type) {
	case T:
		return 1
	case []T:
		return 2
	case map[string]T:
		return 3
	}
	return 0
}

func eqBox[T any](a T, b any) bool { return any(a) == b }

func keys[T comparable](a T, b any) int {
	m := map[any]int{}
	m[a] = 1
	m[b] = 2
	return len(m)
}

// R1
func tparamAssert() int {
	s := 0
	if isInt(int(1)) {
		s += 1
	}
	if isInt(int64(1)) {
		s += 10
	}
	if isInt[A](1) {
		s += 100
	}
	if isT[uint8](byte(1)) {
		s += 1000
	}
	if isT[byte](uint8(1)) {
		s += 10000
	}
	if isT[int](int64(1)) {
		s += 100000
	}
	if isT[[]uint8]([]byte{}) {
		s += 1000000
	}
	if isT[A](int(1)) {
		s += 10000000
	}
	return s // 11011101
}

// A local type as the argument (BUG-092's admitted function-instantiation shape).
func tparamLocalArg() int {
	type L int
	s := 0
	if isInt(L(1)) {
		s += 1
	}
	if isT[L](L(1)) {
		s += 10
	}
	if isT[L](int(1)) {
		s += 100
	}
	if isT[[]L]([]L{}) {
		s += 1000
	}
	return s // 1010
}

// R3
func tparamSwitch() int {
	return sw[byte](uint8(1))*100000 + sw[byte]([]uint8{})*10000 + sw[int](int64(1))*1000 +
		sw[A](map[string]int{})*100 + sw[int]([]int64{})*10 + sw[rune](int32(1)) // 120301
}

// R4
func tparamEqual() int {
	s := 0
	if eqBox(byte(1), uint8(1)) {
		s += 1
	}
	if eqBox(int(1), int64(1)) {
		s += 10
	}
	if eqBox[A](1, int(1)) {
		s += 100
	}
	return s // 101
}

// R5
func tparamMapKeys() int {
	return keys(byte(1), uint8(1))*100 + keys(int(1), int64(1))*10 + keys[A](1, int(1)) // 121
}

// R2: the panic text inside a generic names the argument's kind.
func tparamPanic() int {
	return int(get[int64](any(int(1))))
}

func get[T any](x any) T { return x.(T) }

func main() {}
