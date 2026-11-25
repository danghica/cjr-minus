import Cjr.LinkedList.MergeSort.Correctness
import Cjr.LinkedList.Export
namespace Cjr.LinkedList.MergeSort
open Cjr.Cangjie

def splitDecl : Decl := ⟨"SplitLists",[("left","ListNode"),("right","ListNode")]⟩

def program : Prog := {
  LinkedList.program with
  structs := [splitDecl]
  fns := LinkedList.program.fns ++ [
    {name := "splitList",arg := some "p",body := splitBody,tys := ["ListNode"],ret := "SplitLists"},
    {name := "mergeLists",arg := some "args",body := mergeBody,tys := ["ListNode","ListNode"],ret := "ListNode"},
    {name := "mergeSort",arg := some "p",body := sortBody,tys := ["ListNode"],ret := "ListNode"}]
  main := sortExpr (ofList [5,-1,3,3,0,2])
}
end Cjr.LinkedList.MergeSort
