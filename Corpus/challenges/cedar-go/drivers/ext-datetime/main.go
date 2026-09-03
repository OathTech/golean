// cedar-go census driver: the `datetime` and `duration` extension types —
// parse (time inside), millisecond arithmetic, ordering, print.
// Self-checking. [AGENT] 2026-09-03.
package main

import "cedargo/types"

func censusMain() {
	dt, err := types.ParseDatetime("2024-01-01T00:00:00Z")
	if err != nil {
		panic("parse datetime: " + err.Error())
	}
	if dt.Milliseconds() != 1704067200000 {
		panic("millis")
	}
	later := types.NewDatetimeFromMillis(1704067200000 + 1500)
	if lt, err := dt.LessThan(later); err != nil || !lt {
		panic("ordering")
	}
	if dt.String() != "2024-01-01T00:00:00.000Z" {
		panic("datetime string: " + dt.String())
	}
	d, err := types.ParseDuration("1h30m")
	if err != nil {
		panic("parse duration: " + err.Error())
	}
	if d.ToMinutes() != 90 || d.ToSeconds() != 5400 || d.ToHours() != 1 {
		panic("duration units")
	}
	if d.String() != "1h30m" {
		panic("duration string: " + d.String())
	}
	if _, err := types.ParseDatetime("2024-13-01T00:00:00Z"); err == nil {
		panic("expected invalid month")
	}
	if _, err := types.ParseDuration("1x"); err == nil {
		panic("expected invalid duration")
	}
}

func main() { censusMain() }
