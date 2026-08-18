package main

// spec#Type_definitions block Type_definitions-4-43d28461: a defined type
// (TimeZone int) may have methods; the iota expression -(5 + iota) gives
// EST == -5, CST == -6, MST == -7, PST == -8; String() formats via
// fmt.Sprintf with %+d — EST.String() == "GMT-5h".

import "fmt"

type TimeZone int

const (
	EST TimeZone = -(5 + iota)
	CST
	MST
	PST
)

func (tz TimeZone) String() string {
	return fmt.Sprintf("GMT%+dh", tz)
}

func timezoneStringer() string {
	return EST.String() + "," + PST.String() + "," + string(rune('0'-int(CST)-0)) // "GMT-5h,GMT-8h,6"
}
