package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// PROMOTION at depth 3 and through MIXED hops (value → pointer → value): the
// receiver adjusted through the whole path on the static surface
// (promotedReceiverArg) and walked by the record on the dynamic one
// (receiverAt: `asIs` into a cell, `addr` at a value field, `deref` at a
// pointer field, a nil final pointer passed as the receiver with no panic).

type leaf struct{ n int }

func (l leaf) Get() int { return l.n }
func (l *leaf) Inc()    { l.n++ }

type mid struct{ leaf }
type top struct{ mid }
type outer struct{ top }

type getter interface{ Get() int }
type incer interface{ Inc() }

func depth3Direct() int {
	var o outer
	o.Inc() // (&o.top.mid.leaf).Inc(): addr through three value hops
	o.Inc()
	o.Inc()
	return o.Get()*10 + o.top.mid.leaf.n
}

func depth3Dispatch() int {
	o := outer{top{mid{leaf{n: 4}}}}
	var g getter = o // a value box: the 3-hop path read out of the cell
	var i incer = &o // a pointer box: addr adjust at the end of the path
	i.Inc()
	i.Inc()
	var pg getter = &o
	return g.Get()*100 + pg.Get()*10 + o.top.mid.leaf.n
}

func depth3MethodValues() int {
	o := outer{top{mid{leaf{n: 1}}}}
	f := o.Get     // the leaf copied now
	g := (&o).Inc  // the leaf's address captured
	o.top.mid.leaf.n = 5
	g()
	return f()*10 + o.Get()
}

func depth3MethodExpressions() int {
	o := outer{top{mid{leaf{n: 2}}}}
	ge := outer.Get
	ie := (*outer).Inc
	ie(&o)
	ie(&o)
	return ge(o)
}

type pmid struct{ *leaf }
type ptop struct{ pmid }

func mixedHopsDirect() int {
	t := ptop{pmid{&leaf{n: 10}}}
	t.Inc() // the pointer hop yields the receiver as is
	a := t.Get()
	t.pmid.leaf.n = 20
	return a*100 + t.Get()
}

func mixedHopsDispatch() int {
	t := ptop{pmid{&leaf{n: 1}}}
	var g getter = t  // a VALUE box: the value method derefs at the pointer field
	var i incer = t   // the pointer method is in the value set: the hop is a pointer
	i.Inc()
	var pi incer = &t // and through a pointer box
	pi.Inc()
	return g.Get()*10 + t.leaf.n
}

func mixedHopsMethodExpression() int {
	t := ptop{pmid{&leaf{n: 3}}}
	ie := (*ptop).Inc // a pointer method through a pointer embed: `asIs` at the hop
	ie(&t)
	ve := ptop.Get
	return ve(t)
}

type pbox struct{ *leaf }

func valueMethodPointerEmbedDispatch() int {
	b := pbox{&leaf{n: 6}}
	var g getter = b // deref at the pointer field when dispatched
	b.leaf.n = 8     // the box holds the pointer: the dispatch reads the live leaf
	return g.Get()
}

type nilsafe struct{ n int }

func (p *nilsafe) IsNil() int {
	if p == nil {
		return 1
	}
	return 0
}

type nilbox struct{ *nilsafe }
type isniler interface{ IsNil() int }

func nilPointerEmbedPointerMethodDispatch() int {
	var b nilbox // the embedded pointer is nil
	var i isniler = b
	a := i.IsNil() // the nil pointer IS the receiver: no dereference, no panic
	b.nilsafe = &nilsafe{}
	var j isniler = b
	return a*10 + j.IsNil()
}

func main() {
	depth3Direct()
	depth3Dispatch()
	depth3MethodValues()
	depth3MethodExpressions()
	mixedHopsDirect()
	mixedHopsDispatch()
	mixedHopsMethodExpression()
	valueMethodPointerEmbedDispatch()
	nilPointerEmbedPointerMethodDispatch()
}
