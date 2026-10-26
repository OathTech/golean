package inner

type T struct{ Tag int }

func Local() any { type L int; return L(1) }
