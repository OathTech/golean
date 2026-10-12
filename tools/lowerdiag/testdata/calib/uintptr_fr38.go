// FR-38 / BUG-124 (2026-10-12, fix round LOW-2): `uintptr`'s runtime type
// IDENTITY is refused by name at the frontend (tools/nativefrontend/
// uintptrid.go) wherever a uintptr-mentioning type is boxed into an
// interface or named as an assertion / type-switch target — the decoder
// realizes `uintptr` as `uint64`. The static judge mirrors the rule
// (uintptr.go): uidAssert / uidEqual / uidMapKey / uidTarget / uidMethodSet
// refuse (the first two and the third are three of the release-trust
// review's six probes), uidWidth (width-only) and uidNominal (a defined
// type over uintptr: nominal on the machine) lower.
// TestCalibrationAgainstWire compares each static verdict with the wire;
// TestFloatBitsPrimitiveIsSupplied's map pins the causes and keys.
package main

type uidU uintptr

type uidT struct{}

func (uidT) P() uintptr { return 1 }

func uidAssert() bool   { var x any = uintptr(1); _, ok := x.(uint64); return ok }
func uidEqual() bool    { return any(uintptr(1)) == any(uint64(1)) }
func uidMapKey() int    { return len(map[any]int{uintptr(1): 7, uint64(1): 9}) }
func uidTarget() bool   { var x any = uint64(1); _, ok := x.(uintptr); return ok }
func uidMethodSet() int { var x any = uidT{}; _ = x; return 1 }
func uidWidth() int     { var p uintptr = 40; p += 2; return int(uint64(p) * 3) }
func uidNominal() bool  { var x any = uidU(1); _, ok := x.(uint64); return ok }
