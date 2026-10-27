package zq

// An init with an EMPTY body is no work (pkginit.MakeTask skips it): gc
// emits no record and the frontend's initBodyWork agrees — zq is pruned
// and gates nothing.
func init() {}
