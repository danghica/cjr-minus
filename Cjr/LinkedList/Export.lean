import Cjr.LinkedList.Algebra
import Cjr.Cangjie.Emit

namespace Cjr.LinkedList
open Cjr.Cangjie

def nodeDecl : Decl := ⟨"ListNode", [("nonempty","Bool"),("value","Int64"),("next","ListNode")]⟩
private def bodyOf : Val → Expr | .recE _ _ b => b | _ => .val (.lit .unit)

def program : Prog := {
  classes := [nodeDecl]
  fns := [
    {name := "empty", body := empty, ret := "ListNode"},
    {name := "cons", arg := some "args", body := consBody, tys := ["Int64","ListNode"], ret := "ListNode"},
    {name := "isEmpty", arg := some "p", body := bodyOf isEmptyFn, tys := ["ListNode"], ret := "Bool"},
    {name := "head", arg := some "p", body := bodyOf headFn, tys := ["ListNode"], ret := "Int64"},
    {name := "tail", arg := some "p", body := bodyOf tailFn, tys := ["ListNode"], ret := "ListNode"},
    {name := "length", arg := some "p", body := lengthBody, tys := ["ListNode"], ret := "Int64"},
    {name := "append", arg := some "args", body := appendBody, tys := ["ListNode","ListNode"], ret := "ListNode"},
    {name := "reverseAux", arg := some "args", body := reverseAuxBody, tys := ["ListNode","ListNode"], ret := "ListNode"},
    {name := "reverse", arg := some "p", body := reverseBody, tys := ["ListNode"], ret := "ListNode"}]
  main := lengthExpr (reverseExpr (appendExpr (ofList [1,2,3]) (ofList [4,5])))
}

end Cjr.LinkedList
