package main

import "time"

var maxDatetime = time.Date(292278994, 8, 17, 7, 12, 55, 807*1e6, time.UTC)

// A DEPENDENT initializer whose shape is not effect-isolated (a method
// call on the poisoned value): the export must refuse at the dependency,
// naming maxYear and the poison — never run with maxYear silently zero.
var maxYear = maxDatetime.Year()

func unrelated() int { return 7 }

func main() { println(unrelated(), maxYear) }
