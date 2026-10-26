// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K1 basic kinds: byte ≡ uint8, rune ≡ int32 (aliases); int ≢ int64, uint ≢ uint64,
// float32 ≢ float64.

func byteIsUint8() bool  { var x any = byte(1); _, ok := x.(uint8); return ok }   // true
func uint8IsByte() bool  { var x any = uint8(1); _, ok := x.(byte); return ok }   // true
func runeIsInt32() bool  { var x any = rune('a'); _, ok := x.(int32); return ok } // true
func intIsNotInt64() bool { var x any = int(1); _, ok := x.(int64); return ok }   // false
func uintIsNotUint64() bool { var x any = uint(1); _, ok := x.(uint64); return ok } // false
func f32IsNotF64() bool { var x any = float32(1); _, ok := x.(float64); return ok } // false
func int8IsNotUint8() bool { var x any = int8(1); _, ok := x.(uint8); return ok } // false

// R8: the alias kind inside a slice / map / pointer / func type.
func byteSliceIsUint8Slice() int {
	s := 0
	if _, ok := any([]byte{1}).([]uint8); ok {
		s += 1
	}
	if _, ok := any([]rune{1}).([]int32); ok {
		s += 10
	}
	if _, ok := any(map[byte]rune{}).(map[uint8]int32); ok {
		s += 100
	}
	b := byte(1)
	if _, ok := any(&b).(*uint8); ok {
		s += 1000
	}
	if _, ok := any(func(byte) rune { return 0 }).(func(uint8) int32); ok {
		s += 10000
	}
	if _, ok := any([]byte{1}).([]int8); ok {
		s += 100000
	}
	return s // 11111
}

// R3: one switch over every basic kind; each value's case index is a hex digit.
func basicSwitch() int {
	r := 0
	for _, v := range []any{byte(1), rune(2), int(3), int64(4), uint(5), uint64(6), float32(7), float64(8), true, "s", int8(9), uint16(10)} {
		d := 0
		switch v.(type) {
		case uint8:
			d = 1
		case int32:
			d = 2
		case int:
			d = 3
		case int64:
			d = 4
		case uint:
			d = 5
		case uint64:
			d = 6
		case float32:
			d = 7
		case float64:
			d = 8
		case bool:
			d = 9
		case string:
			d = 10
		case int8, uint16:
			d = 11
		}
		r = r*16 + d
	}
	return r
}

// R3 with alias spellings in the case list.
func basicSwitchAliasCases() int {
	r := 0
	for _, v := range []any{uint8(1), int32(2), int(3)} {
		d := 0
		switch v.(type) {
		case byte:
			d = 1
		case rune:
			d = 2
		case int:
			d = 3
		}
		r = r*10 + d
	}
	return r // 123
}

// R4: == of boxes across the kinds.
func basicEqual() int {
	s := 0
	if any(byte(1)) == any(uint8(1)) {
		s += 1
	}
	if any(rune(1)) == any(int32(1)) {
		s += 10
	}
	if any(int(1)) == any(int64(1)) {
		s += 100
	}
	if any(uint(1)) == any(uint64(1)) {
		s += 1000
	}
	if any(float32(1)) == any(float64(1)) {
		s += 10000
	}
	if any(int8(1)) == any(uint8(1)) {
		s += 100000
	}
	if any(int(1)) == any(int(1)) {
		s += 1000000
	}
	return s // 1000011
}

// R5: map[any] key count — the alias pairs fuse, everything else is its own key.
func basicMapKeys() int {
	m := map[any]int{}
	m[byte(1)] = 1
	m[uint8(1)] = 2
	m[rune(1)] = 3
	m[int32(1)] = 4
	m[int(1)] = 5
	m[int64(1)] = 6
	m[uint(1)] = 7
	m[uint64(1)] = 8
	m[float32(1)] = 9
	m[float64(1)] = 10
	m[int8(1)] = 11
	m[int16(1)] = 12
	m[uint16(1)] = 13
	m[uint32(1)] = 14
	m[true] = 15
	m["1"] = 16
	return len(m)*100 + m[uint8(1)]*10 + m[int32(1)] // 14 keys; 2; 4 → 1424
}

// R2: the display of an alias kind in the panic text (gc prints uint8, not byte).
func basicAssertPanic() int {
	var x any = byte(1)
	return int(x.(rune))
}

func main() {}
