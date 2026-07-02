package main

type depthShadowLeaf struct {
	x int
}

type depthShadowMid struct {
	depthShadowLeaf
}

type depthShadowOuter struct {
	depthShadowMid
	x int
}

func promotedFieldDepthShadow() int {
	o := depthShadowOuter{
		depthShadowMid: depthShadowMid{depthShadowLeaf: depthShadowLeaf{x: 7}},
		x:              3,
	}
	o.x = 4
	o.depthShadowMid.x = 8
	return o.x*10 + o.depthShadowMid.depthShadowLeaf.x
}

func main() {
	promotedFieldDepthShadow()
}
