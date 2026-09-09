package inner

type B int

func (b B) m() int { return 200 + int(b) }
func (b B) é() int { return 800 + int(b) }

type J interface{ m() int }
type Unicode interface{ é() int }

func Read(x J) int              { return x.m() }
func Value(x J) int             { f := x.m; return f() }
func Expr(x J) int              { return J.m(x) }
func Is(x any) bool             { _, ok := x.(J); return ok }
func UnicodeRead(x Unicode) int { return x.é() }

type Q int

func (q *Q) m() int { return 900 + int(*q) }

type H[T ~int] struct{ V T }

func (h H[T]) m() int                              { f := func() int { return 1000 + int(h.V) }; return f() }
func GenericRead[T interface{ m() int }](x T) int  { return x.m() }
func GenericValue[T interface{ m() int }](x T) int { f := x.m; return f() }
