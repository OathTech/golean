// cedar-go census driver: the `decimal` extension type — parse, construct,
// compare, print. Self-checking. [AGENT] 2026-09-03.
package main

import "cedargo/types"

func censusMain() {
	d, err := types.ParseDecimal("12.34")
	if err != nil {
		panic("parse: " + err.Error())
	}
	if d.String() != "12.34" {
		panic("string: " + d.String())
	}
	e, err := types.NewDecimal(1234, -2)
	if err != nil {
		panic("new: " + err.Error())
	}
	if d.Compare(e) != 0 || !d.Equal(e) {
		panic("12.34 != 1234e-2")
	}
	f, _ := types.ParseDecimal("12.35")
	if d.Compare(f) != -1 || f.Compare(d) != 1 {
		panic("ordering")
	}
	if string(d.MarshalCedar()) != `decimal("12.34")` {
		panic("cedar form: " + string(d.MarshalCedar()))
	}
	if _, err := types.ParseDecimal("1.23456"); err == nil {
		panic("expected precision error")
	}
	if _, err := types.ParseDecimal("922337203685477.5808"); err == nil {
		panic("expected overflow error")
	}
	g, _ := types.NewDecimalFromInt(int64(3))
	if g.String() != "3.0" {
		panic("from int: " + g.String())
	}
}

func main() { censusMain() }
