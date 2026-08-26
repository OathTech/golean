import GoLeanProofs.Specs.Raft.HhEquation
open GoLean GoLean.GoCore GoLean.Frame GoLean.RaftSeam
open GoLean.Examples.RaftTwin (twinLowered)
#eval funcListSup twinLowered.funcs.toList
#eval (GoLean.RaftSeam.wBase.functions.size, funcListSup GoLean.RaftSeam.wBase.functions.toList)
