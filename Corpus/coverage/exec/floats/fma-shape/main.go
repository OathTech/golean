package main

// PLATFORM-SENSITIVE BY DESIGN — the fusion-envelope tripwire (floats
// design note 2026-08-04 §3.1). GoCore resolves the Go spec's
// fused-operation latitude to strict per-op rounding, matching gc on
// linux/amd64 with default GOAMD64 (the differential oracle's platform,
// which emits no FMA). The values below discriminate: with per-op
// rounding x*y rounds to exactly -z so r == 0; a fused x*y + z keeps the
// 2^-54-scale residue so r > 0. If this case goes red on a future
// runner (gc/arm64, gc/amd64-v3), that is the tripwire FIRING — the
// oracle platform left the envelope — not noise; see the envelope
// statement in GoLean/GoCore/FloatBits.lean before re-pinning anything.
// The scale factor e defeats compile-time constant folding so the shape
// stays a runtime x*y + z on every platform.
func floatFMAShape(e int) int {
	x := 1 + float64(e)/(1<<27)
	y := x
	z := -(1 + float64(e)/(1<<26))
	r := x*y + z
	score := 0
	if r == 0 {
		score += 1 // per-op rounding (the pinned envelope point)
	}
	if r > 0 {
		score += 10 // fused
	}
	return score
}

func main() {
	floatFMAShape(1)
}
