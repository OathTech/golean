package inner

type T struct{ Tag int }

type Alias = T

type Gen[E any] struct{ v E }

type GenAlias[E any] = Gen[E]
