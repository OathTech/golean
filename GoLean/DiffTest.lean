import GoLean.Runtime

namespace GoLean

structure Observable where
  value : Option GoValue := none
  error : Option GoError := none
  deriving Repr, BEq

def Observable.success (value : GoValue) : Observable :=
  { value := some value }

def Observable.failure (error : GoError) : Observable :=
  { error := some error }

end GoLean
