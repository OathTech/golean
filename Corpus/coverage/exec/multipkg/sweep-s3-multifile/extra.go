package main

import (
	bb "blue/inner"
	zz "red/inner"
)

func fromZZ() any { return zz.T{Tag: 7} }
func fromBB() any { return bb.T{Tag: 7} }

func genFromExtra() any { return zz.Gen[int]{} }

func mkExtraL() any { type L int; return L(1) }

func extraBlueLocal() any { return bb.Local() }

func mkExtraNamed() any {
	type Loc struct{ V int }
	return Loc{3}
}
