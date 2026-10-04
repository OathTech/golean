// The dot-imported float-bits call (TestCalibrationAgainstWire): the frontend
// lowers the QUALIFIED spelling only and refuses this one by name
// (emit.go: "dot-imported math.X called as a bare identifier …").
package main

import . "math"

func fbDot(f float64) uint64 { return Float64bits(f) }
