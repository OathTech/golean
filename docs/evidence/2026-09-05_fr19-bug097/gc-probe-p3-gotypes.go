package main

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
)

const src = `package main
type T int
func (T) Get() int { return 0 }
func (T) get() int { return 0 }
func f() {
	type L int
	var a interface{ Get() int; get() int } = T(1)
	var b interface{ M() L; error }
	var c struct{ X int; Y L "tag" }
	var d interface{ N(L, ...int) (L, error) }
	_, _, _, _ = a, b, c, d
}
`

func main() {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		panic(err)
	}
	conf := types.Config{Importer: importer.Default()}
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{}}
	pkg, err := conf.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		panic(err)
	}
	_ = pkg
	qf := func(p *types.Package) string { return "PATH(" + p.Path() + ")" }
	for id, obj := range info.Defs {
		if v, ok := obj.(*types.Var); ok && len(id.Name) == 1 && id.Name >= "a" && id.Name <= "d" {
			fmt.Printf("%s: nil-qf=%q  qf=%q\n", id.Name, types.TypeString(v.Type(), nil), types.TypeString(v.Type(), qf))
		}
	}
}
