package main
import("fmt"; "go/token"; "go/types")
func main(){
 sig:=types.NewSignatureType(nil,nil,nil,types.NewTuple(),types.NewTuple(),false)
 p:=types.NewPackage("p","p");q:=types.NewPackage("q","q")
 left:=types.NewInterfaceType([]*types.Func{types.NewFunc(token.NoPos,p,"m",sig)},nil).Complete()
 right:=types.NewInterfaceType([]*types.Func{types.NewFunc(token.NoPos,q,"m",sig)},nil).Complete()
 both:=types.NewInterfaceType(nil,[]types.Type{left,right}).Complete()
 fmt.Printf("complete methods=%d methodSet=%v\n",both.NumMethods(),both.IsMethodSet())
 for i:=0;i<both.NumMethods();i++{fmt.Println(both.Method(i).Id())}
}
