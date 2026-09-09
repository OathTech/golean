package inner

type A int

func (a A) m() int { return 100 + int(a) }
func (a A) É() int { return 300 + int(a) }
func (a A) é() int { return 400 + int(a) }
func (a A) 𐐀() int { return 500 + int(a) }

type I interface{ m() int }
type Unicode interface {
	é() int
	É() int
	𐐀() int
}

func Read(x I) int                          { return x.m() }
func Value(x I) int                         { f := x.m; return f() }
func Expr(x I) int                          { return I.m(x) }
func Is(x any) bool                         { _, ok := x.(I); return ok }
func UnicodeRead(x Unicode) (int, int, int) { return x.é(), x.É(), x.𐐀() }
func ConcreteValue(a A) int                 { f := a.m; return f() }
func ConcreteExpr(a A) int                  { return A.m(a) }

type P int

func (p *P) m() int { return 600 + int(*p) }

type G[T ~int] struct{ V T }

func (g G[T]) m() int                              { f := func() int { return 700 + int(g.V) }; return f() }
func GenericRead[T interface{ m() int }](x T) int  { return x.m() }
func GenericValue[T interface{ m() int }](x T) int { f := x.m; return f() }
