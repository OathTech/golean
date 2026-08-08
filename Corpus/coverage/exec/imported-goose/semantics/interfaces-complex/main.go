// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/interfaces_complex.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// source: testdata/examples/semantics/interfaces.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// ----------------------------
// Failing:
// - Slices
// - Maps
// - Empty interface
// - String interface
// ----------------------------

func testParamsInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	volume := measureVolumePlusNM(s, 1, 2)
	return volume == 30
}

func testEmptyInterface() bool {
	var i interface{}
	var j interface{}
	return i == j
}

func testStringInterface() bool {
	var i interface{} = "string"
	var j interface{} = "string"
	return i == j
}

type NumStruct struct {
	Value int
}

func testTypeAssertionInterface() bool {
	var i interface{} = NumStruct{3}
	return i.(NumStruct) == NumStruct{3}
}

type shapeInterface interface {
	describe() string
}

type polygonInterface interface {
	sides() uint64
}

type shapeStruct struct {
	Shape string
}

func (s shapeStruct) describe() string {
	return s.Shape
}

type polygonStruct struct {
	Shape string
	Sides uint64
}

func (p polygonStruct) describe() string {
	return p.Shape
}

func (p polygonStruct) sides() uint64 {
	return p.Sides
}

func testDoublePointerInterface() bool {
	s := shapeStruct{"circle"}
	shapes := []shapeInterface{s, &s}
	s.Shape = "square"
	return shapes[0].describe() != shapes[1].describe()
}

func testMultipleFieldsInterface() bool {
	s := polygonStruct{"triangle", 3}
	return s.Shape == "triangle" && s.Sides == 3
}

type dogInterface interface {
	Name() string
	Speed() uint64
}

type catInterface interface {
	Name() string
	Weight() uint64
}

type Puppy string

func (p Puppy) Name() string {
	return "Max"
}

func (p Puppy) Speed() uint64 {
	return 1
}

type Kitten string

func (k Kitten) Name() string {
	return "Max"
}

func (k Kitten) Weight() uint64 {
	return 10
}

func testSharedFunctionsInterface() bool {
	var kit catInterface = Kitten("Kitten")
	var pup dogInterface = Puppy("Puppy")
	return pup.Name() == kit.Name()
}

type printInterface interface {
	Assign(string)
	GetTitle() string
}

type PaperStruct struct {
	Title string
}

func (p *PaperStruct) Assign(t string) {
	p.Title = t
}

func (p *PaperStruct) GetTitle() string {
	return p.Title
}

func testAcceptAddressInterface() bool {
	var p1 PaperStruct
	var p2 PaperStruct
	p1.Assign("Sample Title")
	p2.Assign("Sample Title")
	var print1 printInterface
	var print2 printInterface
	print1 = &p1
	print2 = &p2
	return print1.GetTitle() == print2.GetTitle()
}

type Flower interface {
	Petals() uint64
}

type Flora interface {
	Flower
	Genus() string
}

type Lily struct{}

func (l Lily) Petals() uint64 { return 3 }
func (l Lily) Genus() string  { return "Lillium" }

type Rose struct{}

func (r Rose) Petals() uint64 { return 12 }
func (r Rose) Genus() string  { return "Rosa" }

type Daisy struct{}

func (d Daisy) Petals() uint64 { return 5 }
func (d Daisy) Genus() string  { return "Bellis" }

func testPolymorphismInterface() bool {
	l := new(Lily)
	r := new(Rose)
	d := new(Daisy)
	f := [...]Flower{l, r, d}
	return f[0].Petals() == 3
}

func testEmbeddingInterface() bool {
	l := new(Lily)
	r := new(Rose)
	d := new(Daisy)
	f := [...]Flora{l, r, d}
	return f[0].Petals() == 3
}

func testDowncastInterface() bool {
	l := Lily{}
	var f Flora = l
	return f.Petals() == f.(Flower).Petals()
}


// ----------------------------
// SETUP
// ----------------------------

type geometryInterface interface {
	Square() uint64
	Volume() uint64
}

func measureArea(t geometryInterface) uint64 {
	return t.Square()
}

func measureVolumePlusNM(t geometryInterface, n uint64, m uint64) uint64 {
	return t.Volume() + n + m
}

func measureVolume(t geometryInterface) uint64 {
	return t.Volume()
}

type SquareStruct struct {
	Side uint64
}

func (t SquareStruct) Square() uint64 {
	return t.Side * t.Side
}

func (t SquareStruct) Volume() uint64 {
	return t.Side * t.Side * t.Side
}

// ----------------------------
// TESTS
// ----------------------------

func testBasicInterface() bool {
	s := SquareStruct{
		Side: 2,
	}
	return measureArea(s) == 4
}

func testAssignInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	area := measureArea(s)
	return area == 9
}

func testMultipleInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureArea(s)
	return square1 == square2
}

func testBinaryExprInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureVolume(s)
	return square1 == measureArea(s) && square2 == measureVolume(s)
}

func testIfStmtInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	if measureArea(s) == 9 {
		return true
	}
	return false
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestParamsInterface() int {
	if testParamsInterface() {
		return 1
	}
	return 0
}

func goleanTestEmptyInterface() int {
	if testEmptyInterface() {
		return 1
	}
	return 0
}

func goleanTestStringInterface() int {
	if testStringInterface() {
		return 1
	}
	return 0
}

func goleanTestTypeAssertionInterface() int {
	if testTypeAssertionInterface() {
		return 1
	}
	return 0
}

func goleanTestDoublePointerInterface() int {
	if testDoublePointerInterface() {
		return 1
	}
	return 0
}

func goleanTestMultipleFieldsInterface() int {
	if testMultipleFieldsInterface() {
		return 1
	}
	return 0
}

func goleanTestSharedFunctionsInterface() int {
	if testSharedFunctionsInterface() {
		return 1
	}
	return 0
}

func goleanTestAcceptAddressInterface() int {
	if testAcceptAddressInterface() {
		return 1
	}
	return 0
}

func goleanTestPolymorphismInterface() int {
	if testPolymorphismInterface() {
		return 1
	}
	return 0
}

func goleanTestEmbeddingInterface() int {
	if testEmbeddingInterface() {
		return 1
	}
	return 0
}

func goleanTestDowncastInterface() int {
	if testDowncastInterface() {
		return 1
	}
	return 0
}

func goleanTestBasicInterface() int {
	if testBasicInterface() {
		return 1
	}
	return 0
}

func goleanTestAssignInterface() int {
	if testAssignInterface() {
		return 1
	}
	return 0
}

func goleanTestMultipleInterface() int {
	if testMultipleInterface() {
		return 1
	}
	return 0
}

func goleanTestBinaryExprInterface() int {
	if testBinaryExprInterface() {
		return 1
	}
	return 0
}

func goleanTestIfStmtInterface() int {
	if testIfStmtInterface() {
		return 1
	}
	return 0
}

func main() {}
