import Cjr.Cangjie.Emit
import Cjr.Examples

namespace Cjr.Cangjie.Examples
open Cjr.Examples (int)

def unit : Expr := .val (.lit .unit)
def v (n : Int) : Val := .lit (.int n)
def cellS : Decl := ⟨"Cell", [("x", "Int64")]⟩
def boxC : Decl := ⟨"Box", [("value", "Int64")]⟩
def counterC : Decl := ⟨"Counter", [("value", "Int64")]⟩
def vtableS : Decl := ⟨"VTable", [("inc", "(Counter) -> Unit")]⟩
def nodeC : Decl := ⟨"Node", [("isCons", "Bool"), ("value", "Int64"), ("next", "Node")]⟩

def sumOne : Expr := .varBind "n" (int 1) (.varBind "s" (int 0)
  (.seq (.whileE (.binOp .le (int 1) (.var "n"))
    (.seq (.assign "s" (.binOp .plus (.var "s") (int 1)))
          (.assign "n" (.binOp .minus (.var "n") (int 1))))) (.var "s")))
def binaryBody (op : BinOp) : Expr :=
  .letE (some "a") (.structLoad (.var "args") 0)
    (.letE (some "b") (.structLoad (.var "args") 1) (.binOp op (.var "a") (.var "b")))
def arith : Prog := {fns := [
  {name := "sumOne", body := sumOne, ret := "Int64"},
  {name := "multiply", arg := some "args", body := binaryBody .mul, tys := ["Int64", "Int64"], ret := "Int64"},
  {name := "divide", arg := some "args", body := binaryBody .div, tys := ["Int64", "Int64"], ret := "Int64"}], main := sumOne}

def bump : Expr := .varBind "p" (.val (.struct [v 0]))
  (.seq (.structStore "p" 0 (int 1)) (.structLoad (.var "p") 0))
def bumpKeep : Expr := .letE (some "r") (.alloc (int 1)) (.seq bump (.load (.var "r")))
def structUpd : Prog := {structs := [cellS], fns := [
  {name := "bump", body := bump, ret := "Int64"},
  {name := "bumpKeep", body := bumpKeep, ret := "Int64"}], main := bumpKeep}

def cellBody : Expr := .letE (some "p") (.alloc (int 1))
  (.seq (.store (.var "p") (int 7)) (.seq (.load (.var "p")) (.free (.var "p"))))
def cell : Prog := {fns := [{name := "cell", body := cellBody}], main := cellBody}

def classBump : Expr := .letE (some "r") (.alloc (int 1))
  (.letE (some "o") (.new [v 0] [])
    (.seq (.fieldStore (.var "o") 0 (int 5)) (.seq (.fieldLoad (.var "o") 0) (.load (.var "r")))))
def classUpd : Prog := {classes := [boxC], fns := [{name := "classBump", body := classBump, ret := "Int64"}], main := classBump}

def incBody : Expr := .fieldStore (.var "this") 0 (.binOp .plus (.fieldLoad (.var "this") 0) (int 1))
def vtableBody : Expr := .letE (some "inc") (.recE none (some "this") incBody)
  (.letE (some "box") (.struct [] [.var "inc"])
    (.letE (some "o") (.new [v 0] [])
      (.seq (.app (.structLoad (.var "box") 0) (.var "o")) (.fieldLoad (.var "o") 0))))
def vtable : Prog := {classes := [counterC], structs := [vtableS], fns := [
  {name := "inc", arg := some "this", body := incBody, tys := ["Counter"]},
  {name := "run", body := vtableBody, ret := "Int64"}], main := vtableBody}

def swapAt (l₁ l₂ : Int) : Expr := .letE (some "t") (.load (.val (.lit (.ptr l₁))))
  (.seq (.store (.val (.lit (.ptr l₁))) (.load (.val (.lit (.ptr l₂)))))
        (.store (.val (.lit (.ptr l₂))) (.var "t")))
def swapBody : Expr := .letE (some "l1") (.structLoad (.var "args") 0)
  (.letE (some "l2") (.structLoad (.var "args") 1) (renamePtr 0 "l1" (renamePtr 1 "l2" (swapAt 0 1))))
def swap : Prog := {fns := [{name := "swap", arg := some "args", body := swapBody, tys := ["CPointer<Int64>", "CPointer<Int64>"]}], main := .letE (some "l1") (.alloc (int 1)) (.letE (some "l2") (.alloc (int 1))
    (.seq (.store (.var "l1") (int 1)) (.seq (.store (.var "l2") (int 2))
      (.app (.recE none (some "args") swapBody) (.struct [] [.var "l1", .var "l2"]))))) }

def sumAt (p : Int) : Expr := .varBind "i" (int 0) (.varBind "s" (int 0)
  (.seq (.whileE (.binOp .le (.var "i") (int 0))
    (.seq (.assign "s" (.binOp .plus (.var "s") (.load (.offset (.val (.lit (.ptr p))) (.var "i")))))
          (.assign "i" (.binOp .plus (.var "i") (int 1))))) (.var "s")))
def sumAtBody : Expr := renamePtr 0 "p" (sumAt 0)
def sumBlock : Prog := {fns := [{name := "sumAt", arg := some "p", body := sumAtBody, tys := ["CPointer<Int64>"], ret := "Int64"}], main := .letE (some "p") (.alloc (int 1)) (.seq (.store (.var "p") (int 4))
    (.app (.recE none (some "p") sumAtBody) (.var "p")))}

def writeBody : Expr := .store (.var "x") (int 9)
def writeCall (p q : Int) : Expr := .letE (some "f") (.recE none (some "x") writeBody)
  (.seq (.app (.var "f") (.val (.lit (.ptr p)))) (.load (.val (.lit (.ptr q)))))
def frameBody : Expr := .letE (some "p") (.structLoad (.var "args") 0)
  (.letE (some "q") (.structLoad (.var "args") 1) (renamePtr 0 "p" (renamePtr 1 "q" (writeCall 0 1))))
def frameCall : Prog := {fns := [
  {name := "write", arg := some "x", body := writeBody, tys := ["CPointer<Int64>"]},
  {name := "frameCall", arg := some "args", body := frameBody, tys := ["CPointer<Int64>", "CPointer<Int64>"], ret := "Int64"}], main := .letE (some "p") (.alloc (int 1)) (.letE (some "q") (.alloc (int 1))
    (.seq (.store (.var "q") (int 3)) (.app (.recE none (some "args") frameBody) (.struct [] [.var "p", .var "q"]))))}

/-- The eight monomorphic upstream `emit_cj.v` fixtures. -/
def upstream : List (String × Prog) := [
  ("arith", arith), ("struct_upd", structUpd), ("cell", cell), ("swap", swap),
  ("sum_block", sumBlock), ("class_upd", classUpd), ("frame_call", frameCall), ("vtable", vtable)]

def factorial : Prog := {fns := [{name := "fact", arg := some "n", body := match Cjr.Examples.factorial with | .recE _ _ b => b | _ => unit, tys := ["Int64"], ret := "Int64"}], main := .app Cjr.Examples.factorial (int 5)}
def method : Prog := {classes := [counterC], fns := [
  {name := "inc", owner := some "Counter", arg := some "this", body := incBody}], main := .letE (some "o") (.new [v 0] []) (.app (.recE none (some "this") incBody) (.var "o"))}
def selfReference : Prog := {classes := [nodeC], main := .letE (some "n") (.new [] [.val (.lit (.bool false)), int 0, unit]) (.fieldLoad (.var "n") 2)}
def strictAndBody : Expr := .varBind "x" (int 0)
  (.seq (.binOp .and (.val (.lit (.bool false)))
    (.seq (.assign "x" (int 1)) (.val (.lit (.bool true))))) (.var "x"))
def strictAnd : Prog := {fns := [{name := "strictAnd", body := strictAndBody, ret := "Int64"}], main := strictAndBody}
def programs : List (String × Prog) := upstream ++ [
  ("factorial", factorial), ("method", method), ("self_reference", selfReference), ("strict_and", strictAnd),
  ("counter", {fns := [{name := "runCounter", body := Cjr.Examples.counter, ret := "Int64"}], main := Cjr.Examples.counter}), ("raw", {fns := [{name := "runRaw", body := Cjr.Examples.rawRoundTrip, ret := "Int64"}], main := Cjr.Examples.rawRoundTrip})]
end Cjr.Cangjie.Examples
