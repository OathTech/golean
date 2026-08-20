package liberr

import "errors"

// ErrShared is the raft-sentinel shape: a package-level errors.New
// global in a non-main unit, discriminated by identity from outside.
var ErrShared = errors.New("shared sentinel")

func Give() error { return ErrShared }

func IsShared(err error) bool { return err == ErrShared }
