package main

import (
 "go/ast"
 "go/parser"
 "go/token"
 "go/types"
 "testing"
)

func TestIndependentDeclarationIdentity(t *testing.T) {
 e,_:=checkSource(t, `package main
 type R struct { Next *R }
 type S struct { Next *S }
 type A[T any] = []T
 type G[T any] struct { X T }
 type H[T any] struct { X T }
 type I interface { M(int) string }
 type J interface { I; N() }
 type K interface { M(int) string; N() }
 type B int
 var r *R; var r2 *R; var s *S
 var g G[A[int]]; var g2 G[[]int]; var g3 G[[]B]; var h H[[]int]
 var j interface { I; N() }; var k interface { M(int) string; N() }
 var namedJ J; var namedK K
 var v struct { R }; var v2 struct { R R }
 var e1 error; var e2 interface { Error() string }
 var b bool; var i int; var a [0]G[complex64]
 func main() {}
 `)
 names:=[]string{"r","r2","s","g","g2","g3","h","j","k","namedJ","namedK","v","v2","e1","e2","b","i","a"}
 for _,a:=range names { for _,b:=range names {
   l,r:=varType(t,e,a),varType(t,e,b)
   if got,want:=declarationJSON(t,e,l)==declarationJSON(t,e,r),types.Identical(l,r);got!=want {t.Fatalf("%s/%s: got %v want %v",a,b,got,want)}
 }}
 t.Logf("%d pairwise identity comparisons",len(names)*len(names))
}

func TestIndependentDeclarationReceiverAndSubstitution(t *testing.T) {
 p:=types.NewPackage("example.org/p","p")
 empty:=types.NewTuple()
 arg:=types.NewTuple(types.NewParam(token.NoPos,p,"v",types.Typ[types.Bool]))
 rec:=types.NewVar(token.NoPos,p,"self",types.NewPointer(types.Typ[types.Int]))
 with:=types.NewSignatureType(rec,nil,nil,arg,empty,false)
 without:=types.NewSignatureType(nil,nil,nil,arg,empty,false)
 e:=&emitter{}
 if declarationJSON(t,e,with)!=declarationJSON(t,e,without) {t.Fatal("receiver leaked into function identity")}
 tp:=types.NewTypeParam(types.NewTypeName(token.NoPos,nil,"T",nil),types.NewInterfaceType(nil,nil).Complete())
 e.curSubst=map[*types.TypeParam]types.Type{tp:types.Typ[types.Complex128]}
 if declarationJSON(t,e,types.NewSlice(tp))!=declarationJSON(t,e,types.NewSlice(types.Typ[types.Complex128])) {t.Fatal("substitution lost")}
 e.curSubst=map[*types.TypeParam]types.Type{}
 if value,err:=e.emitDeclarationType(types.NewSlice(tp));err==nil||value!=nil {t.Fatalf("unbound substitution accepted: %v %v",value,err)}
}

func TestIndependentDeclarationLocalStencil(t *testing.T) {
 src:=`package main
 func F[T any]() { type Local bool; var x Local; _ = x }
 func main() {}
 `
 fset:=token.NewFileSet()
 file,err:=parser.ParseFile(fset,"main.go",src,0);if err!=nil {t.Fatal(err)}
 info:=&types.Info{Types:map[ast.Expr]types.TypeAndValue{},Defs:map[*ast.Ident]types.Object{},Uses:map[*ast.Ident]types.Object{}}
 config:=types.Config{}
 pkg,err:=config.Check("main",fset,[]*ast.File{file},info);if err!=nil {t.Fatal(err)}
 e:=&emitter{fset:fset,pkg:pkg,info:info}
 ty:=varType(t,e,"x")
 e.curInstDecl=file.Decls[0].(*ast.FuncDecl)
 e.curTargs=[]types.Type{types.Typ[types.Int]};left:=declarationJSON(t,e,ty)
 e.curTargs=[]types.Type{types.Typ[types.Bool]};right:=declarationJSON(t,e,ty)
 if left==right {t.Fatalf("local types in distinct enclosing stencils merged: %s",left)}
 t.Log(left,right)
}
