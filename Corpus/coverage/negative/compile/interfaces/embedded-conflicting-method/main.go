package main

type conflictingEmbeddedA interface {
	m() int
}

type conflictingEmbeddedB interface {
	m() string
}

type conflictingEmbeddedBoth interface {
	conflictingEmbeddedA
	conflictingEmbeddedB
}
