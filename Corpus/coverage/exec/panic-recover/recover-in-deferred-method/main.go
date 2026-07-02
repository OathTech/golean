package main

type deferredMethodRecoverer struct{}

func (deferredMethodRecoverer) capture(dst *int) {
	if recover() != nil {
		*dst = 5
	}
}

func recoverInDeferredMethod() (result int) {
	var r deferredMethodRecoverer
	defer r.capture(&result)
	panic("method recover")
}
