package zq

// The BUG-061 witness's shape (an array literal gc folds; the frontend
// cannot tell) — here imported by BOTH competitors, so whether it is a
// node moves neither of them.
var A = [3]int{1, 2, 3}
