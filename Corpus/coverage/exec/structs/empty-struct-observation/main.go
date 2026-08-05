package main

// The observation channel's contract is reflect.Type.Name(): "" for any
// NON-DEFINED type. The canonical anonymous struct{} is not a defined
// type, so the Go harness renders typeName "" — the machine used to
// render the internal key "struct{}" verbatim, a naming-only
// differential FAIL on any case whose observed value contains a bare
// struct{} (directly, as a field, or as an array element). Arc-final
// audit F7 (2026-08-06), red-first.

type esoHolder struct {
	E struct{}
	N int
}

func emptyStructDirect() struct{} {
	return struct{}{}
}

func emptyStructField() esoHolder {
	return esoHolder{N: 7}
}

func emptyStructArray() [2]struct{} {
	return [2]struct{}{}
}

// CONTROL: a NAMED empty struct is a defined type — Name() is the name.
type esoNamed struct{}

func emptyStructNamed() esoNamed {
	return esoNamed{}
}
