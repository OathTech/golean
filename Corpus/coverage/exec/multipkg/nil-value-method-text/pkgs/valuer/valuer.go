// Package valuer — the receiver type of BUG-087's multi-package rendering
// row lives OUTSIDE main, under the import path `pkgs/valuer`, so gc's
// panicwrap text qualifies it by the PATH: `value method pkgs/valuer.T.Val
// called using nil *T pointer` (runtime/error.go panicwrap parses the
// wrapper SYMBOL `pkgs/valuer.(*T).Val`).
package valuer

type T struct{ V int }

func (t T) Val() int { return t.V }
