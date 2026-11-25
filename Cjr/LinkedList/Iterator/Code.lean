import Cjr.LinkedList.Correctness

namespace Cjr.LinkedList.Iterator

def optionNode : Option Loc → Val
  | none => .struct [flag false,.lit .unit]
  | some p => .struct [flag true,reference p]

/-- Field 0 owns a reference to the original list; field 1 is the roving cursor. -/
def create (p : Loc) : Expr := .new [reference p,reference p] []
def createBody : Expr := .new [] [.var "list",.var "list"]
def createFn : Val := .recE none (some "list") createBody
def createCall (p : Loc) : Expr := .app (.val createFn) (refExpr p)

/-- Return the current nonempty node, then advance to its tail. Empty sentinels
are never returned. The exhausted branch does not write any field. -/
def nextBody : Expr :=
  .letE (some "p") (.fieldLoad (.var "self") 1)
    (.ifE (.fieldLoad (.var "p") 0)
      (.seq (.fieldStore (.var "self") 1 (.fieldLoad (.var "p") 2))
        (.struct [flag true] [.var "p"]))
      (.val (optionNode none)))
def nextFn : Val := .recE none (some "self") nextBody
def next (it : Loc) : Expr := .app (.val nextFn) (refExpr it)

def advance (s : State) (it q : Loc) : State :=
  {s with obj := s.obj.insert (⟨it⟩,1) (reference q)}
def created (s : State) (p : Loc) : State :=
  {s with obj := (initFields s.next [reference p,reference p] 0).union s.obj,next := s.next+1}
end Cjr.LinkedList.Iterator
