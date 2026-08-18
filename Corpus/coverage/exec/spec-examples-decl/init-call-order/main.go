package main

// spec#Order_of_evaluation block Order_of_evaluation-3-af118e1b: at package
// level, initialization dependencies override the left-to-right rule for
// individual initialization expressions but NOT for operands within each
// expression — the calls happen in the order u(), sqr(), v(), f(), v(), g().
// The spec declares u and v only as "independent"; they are realized here as
// recorders returning 2 and 3, making the values a == 10, b == 10, c == 7.

var seq string

var a, b, c = f() + v(), g(), sqr(u()) + v()

func f() int { seq += "f;"; return c }

func g() int { seq += "g;"; return a }

func sqr(x int) int { seq += "sqr;"; return x * x }

// functions u and v are independent of all other variables and functions
func u() int { seq += "u;"; return 2 }

func v() int { seq += "v;"; return 3 }

func initCallOrder() string { return seq } // "u;sqr;v;f;v;g;"

func initCallValues() int { return a*100 + b*10 + c } // 1107
