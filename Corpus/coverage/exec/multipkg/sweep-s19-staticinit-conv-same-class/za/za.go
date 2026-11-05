package za

// int -> int64 on amd64: types.SimType[TINT] == TINT64, so
// typecheck.Convertop answers OCONVNOP (case 4) and staticinit's
// staticcopy folds the copy of the static global zv. gc: no record.
var zv = 3
var C = int64(zv)
