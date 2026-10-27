package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// GENERIC carriers: an instantiation's method set at the dynamic routes
// (satisfaction, one-value assertion, type switch, dispatch), a pointer method
// on an instantiation (auto `&`, a `*Box[int]` box), promotion through an
// instantiated embedded generic type, method expressions on an instantiation,
// the pointer-constraint idiom, a constraint met by PROMOTION, a type-parameter
// method value stored and called later, and a type-parameter value boxed to
// `any` then asserted back to its constraint.

type box[T any] struct{ v T }

func (b box[T]) Get() T  { return b.v }
func (b *box[T]) Set(v T) { b.v = v }

type intGetter interface{ Get() int }
type intSetter interface{ Set(int) }

func instantiationSatisfies() int {
	var x any = box[int]{v: 4}
	_, ok := x.(intGetter)
	g := x.(intGetter)
	var y any = box[string]{v: "s"}
	_, okStr := y.(intGetter) // Get() string is not Get() int
	r := g.Get()
	switch x.(type) {
	case intSetter:
		r += 100
	case intGetter:
		r += 200
	}
	if ok {
		r += 1000
	}
	if okStr {
		r += 10000
	}
	return r
}

func instantiationPointerMethod() int {
	var b box[int]
	b.Set(3) // (&b).Set(3)
	var s intSetter = &b
	s.Set(5)
	var g intGetter = &b // *box[int] ⊇ box[int]'s value methods
	return g.Get()*10 + b.v
}

type pair[T any] struct {
	box[T]
	other T
}

func genericEmbeddingPromotion() int {
	p := pair[int]{box[int]{v: 1}, 2}
	p.Set(6) // promoted through the instantiated embedded field
	var g intGetter = p
	var x any = &p
	_, ok := x.(intSetter)
	r := g.Get()*10 + p.Get()
	if ok {
		r += 100
	}
	return r
}

func instantiationMethodExpression() int {
	b := box[int]{v: 2}
	get := box[int].Get
	set := (*box[int]).Set
	set(&b, 9)
	return get(b)
}

type counter struct{ n int }

func (c *counter) Inc() { c.n++ }

func bump[T any, PT interface {
	*T
	Inc()
}](n int) T {
	var t T
	for i := 0; i < n; i++ {
		PT(&t).Inc()
	}
	return t
}

func pointerConstraintIdiom() int {
	c := bump[counter](4)
	return c.n
}

type inner struct{ n int }

func (i inner) Val() int { return i.n }

type outer struct{ inner }

type valer interface{ Val() int }

func callVal[T valer](x T) int { return x.Val() }

func constraintByPromotion() int {
	return callVal(outer{inner{n: 8}})*10 + callVal[valer](outer{inner{n: 1}})
}

func storeAndBox[T valer](x T) int {
	f := x.Val // a method value through the type parameter
	var a any = x
	v, ok := a.(valer)
	r := f()
	if ok {
		r += v.Val() * 10
	}
	return r
}

func typeparamMethodValueAndBox() int {
	return storeAndBox(inner{n: 3})*100 + storeAndBox(outer{inner{n: 2}})
}

func main() {
	instantiationSatisfies()
	instantiationPointerMethod()
	genericEmbeddingPromotion()
	instantiationMethodExpression()
	pointerConstraintIdiom()
	constraintByPromotion()
	typeparamMethodValueAndBox()
}
