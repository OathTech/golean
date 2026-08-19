package zst

// STATICALLY initialized: `5` is a constant, so cmd/compile's
// staticinit pass folds the assignment into the data section, the
// synthetic init function's body comes out empty, and MakeTask emits
// NO `..inittask` record. zst is therefore not a node of gc's
// schedule, and `sm` — which imports it — is ready at step one.
var X = 5
