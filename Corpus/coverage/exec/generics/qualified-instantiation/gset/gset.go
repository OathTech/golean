package gset

// gset is the case-local SOURCE package whose generic functions the
// subject instantiates EXPLICITLY through the package qualifier
// (`gset.Immutable[string](...)`) — FR-27's shape (cedar-go's
// `mapset.Immutable[EntityUID](args...)`, types/entity_uid.go:143).

// Set is a generic set over a comparable element type.
type Set[T comparable] struct {
	m map[T]struct{}
}

// Make builds a Set from its arguments (cedar-go's mapset.Make twin).
func Make[T comparable](xs ...T) Set[T] {
	s := Set[T]{m: map[T]struct{}{}}
	for _, x := range xs {
		s.m[x] = struct{}{}
	}
	return s
}

// Len is the element count.
func (s Set[T]) Len() int { return len(s.m) }

// Contains reports membership.
func (s Set[T]) Contains(x T) bool {
	_, ok := s.m[x]
	return ok
}

// ImmutableSet wraps a Set behind a read-only method set.
type ImmutableSet[T comparable] struct {
	s Set[T]
}

// Immutable builds an ImmutableSet (cedar-go's mapset.Immutable twin —
// variadic, so the explicit instantiation is the natural spelling when
// the caller has no argument to infer from).
func Immutable[T comparable](xs ...T) ImmutableSet[T] {
	return ImmutableSet[T]{s: Make(xs...)}
}

// Len is the element count.
func (s ImmutableSet[T]) Len() int { return s.s.Len() }

// Box is a generic wrapper type — the operand of the NESTED
// instantiation `gset.Wrap[gset.Box[int]](...)`.
type Box[T any] struct {
	V T
}

// Wrap boxes a value.
func Wrap[T any](v T) Box[T] { return Box[T]{V: v} }

// Apply is a two-parameter generic: the IndexListExpr spelling
// `gset.Apply[int, gset.Box[int]](gset.Wrap[int], 3)`.
func Apply[T, U any](f func(T) U, x T) U { return f(x) }

// Sum over an integer type set.
func Sum[T ~int | ~int64](xs []T) T {
	var acc T
	for _, x := range xs {
		acc += x
	}
	return acc
}
