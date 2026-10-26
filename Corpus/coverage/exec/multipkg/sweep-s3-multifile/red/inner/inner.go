package inner

type T struct{ Tag int }

type Gen[E any] struct{ v E }

// MakeGen instantiates Gen[int] INSIDE its own package; main's Gen[int] spelling is the same type.
func MakeGen() any { return Gen[int]{v: 1} }

// MakeGenT instantiates Gen at this package's T.
func MakeGenT() any { return Gen[T]{} }

func Local() any { type L int; return L(1) }
