package main
import("fmt";"go/ast";"go/parser";"go/token";"go/types")
type importer map[string]*types.Package
func (i importer) Import(p string)(*types.Package,error){if p:=i[p];p!=nil{return p,nil};return nil,fmt.Errorf("missing package")}
func check(path,source string,im importer)*types.Package{
 fset:=token.NewFileSet();file,err:=parser.ParseFile(fset,path+".go",source,0);if err!=nil{panic(err)}
 cfg:=types.Config{Importer:im};p,err:=cfg.Check(path,fset,[]*ast.File{file},nil);if err!=nil{panic(err)};return p
}
func main(){
 im:=importer{};im["p"]=check("p","package p; type I interface { m() }",im);im["q"]=check("q","package q; type I interface { m() }",im)
 p:=check("main","package main; import \"p\"; import \"q\"; type Mix interface { p.I; q.I }; func Main() {}",im)
 iface:=p.Scope().Lookup("Mix").Type().Underlying().(*types.Interface).Complete()
 fmt.Printf("actual source accepted; complete methods=%d methodSet=%v\n",iface.NumMethods(),iface.IsMethodSet())
 for i:=0;i<iface.NumMethods();i++{fmt.Println(iface.Method(i).Id())}
}
