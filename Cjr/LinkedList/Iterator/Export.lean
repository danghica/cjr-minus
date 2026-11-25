import Cjr.LinkedList.Iterator.Correctness
import Cjr.LinkedList.Export
namespace Cjr.LinkedList.Iterator
open Cjr.Cangjie

def iteratorDecl : Decl := ⟨"ListIterator",[("list","ListNode"),("cursor","ListNode")]⟩
def optionDecl : Decl := ⟨"NodeOption",[("isSome","Bool"),("node","ListNode")]⟩

def program : Prog := {
  LinkedList.program with
  classes := [nodeDecl,iteratorDecl]
  structs := [optionDecl]
  nativeOptions := [("NodeOption","ListNode")]
  fns := LinkedList.program.fns ++ [
    {name := "iterator",arg := some "list",body := createBody,tys := ["ListNode"],ret := "ListIterator"},
    {name := "next",owner := some "ListIterator",arg := some "self",body := nextBody,ret := "NodeOption"}]
  main := .letE (some "it") (.app (.val createFn) (ofList [1,2,3]))
    (.letE (some "opt") (.app (.val nextFn) (.var "it"))
      (.ifE (.structLoad (.var "opt") 0)
        (.fieldLoad (.structLoad (.var "opt") 1) 1) (integer (-1))))
}
end Cjr.LinkedList.Iterator
