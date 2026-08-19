package ce

import (
	// sync/atomic has NO initialization work of its own — it is
	// intrinsics and type wrappers — so gc emits no inittask for it
	// and this blank import gates nothing. (Contrast `sync`, which
	// does have work: multipkg/init-order-stdlib.)
	_ "sync/atomic"

	"rec"
)

var V = rec.Push(1)
