import Cjr.Execution

namespace Cjr.LinkedList

def integer (n : Int) : Expr := .val (.lit (.int n))
def reference (p : Loc) : Val := .lit (.obj p)
def refExpr (p : Loc) : Expr := .val (reference p)
def flag (b : Bool) : Val := .lit (.bool b)

/-- A sentinel represents empty. Nonempty nodes store [true, head, tail].
Nodes are persistent: operations never mutate an existing node. -/
def empty : Expr := .new [flag false, .lit (.int 0), .lit .unit] []
def cons (x : Int) (p : Loc) : Expr := .new [flag true, .lit (.int x), reference p] []
def head (p : Loc) : Expr := .fieldLoad (refExpr p) 1
def tail (p : Loc) : Expr := .fieldLoad (refExpr p) 2
def isEmpty (p : Loc) : Expr :=
  .ifE (.fieldLoad (refExpr p) 0) (.val (flag false)) (.val (flag true))

def lengthBody : Expr :=
  .ifE (.fieldLoad (.var "p") 0)
    (.binOp .plus (integer 1) (.app (.var "length") (.fieldLoad (.var "p") 2)))
    (integer 0)
def lengthFn : Val := .recE (some "length") (some "p") lengthBody
def length (p : Loc) : Expr := .app (.val lengthFn) (refExpr p)

/-- Argument packs let the implementation use ordinary first-order Cangjie signatures. -/
def appendBody : Expr :=
  .letE (some "p") (.structLoad (.var "args") 0)
    (.letE (some "q") (.structLoad (.var "args") 1)
      (.ifE (.fieldLoad (.var "p") 0)
        (.new [] [.val (flag true), .fieldLoad (.var "p") 1,
          .app (.var "append") (.struct [] [.fieldLoad (.var "p") 2, .var "q"])])
        (.var "q")))
def appendFn : Val := .recE (some "append") (some "args") appendBody
def pair (p q : Loc) : Val := .struct [reference p, reference q]
def append (p q : Loc) : Expr := .app (.val appendFn) (.val (pair p q))

def reverseAuxBody : Expr :=
  .letE (some "p") (.structLoad (.var "args") 0)
    (.letE (some "q") (.structLoad (.var "args") 1)
      (.ifE (.fieldLoad (.var "p") 0)
        (.app (.var "reverseAux")
          (.struct [] [.fieldLoad (.var "p") 2,
            .new [] [.val (flag true), .fieldLoad (.var "p") 1, .var "q"]]))
        (.var "q")))
def reverseAuxFn : Val := .recE (some "reverseAux") (some "args") reverseAuxBody
def reverseAux (p q : Loc) : Expr := .app (.val reverseAuxFn) (.val (pair p q))
def reverse (p : Loc) : Expr := .letE (some "nil") empty
  (.app (.val reverseAuxFn) (.struct [] [refExpr p, .var "nil"]))

/-- A closed CJR construction of any finite test input; operations themselves are recursive CJR functions. -/
def ofList : List Int → Expr
  | [] => empty
  | x :: xs => .letE (some "xs") (ofList xs)
      (.new [] [.val (flag true), integer x, .var "xs"])

/-- Callable wrappers used by native extraction; their specialization is proved
against the same constructors and observers as the abstract interface. -/
def consBody : Expr :=
  .letE (some "x") (.structLoad (.var "args") 0)
    (.letE (some "xs") (.structLoad (.var "args") 1)
      (.new [] [.val (flag true), .var "x", .var "xs"]))
def consFn : Val := .recE none (some "args") consBody
def consCall (x : Int) (p : Loc) : Expr :=
  .app (.val consFn) (.val (.struct [.lit (.int x),reference p]))
def headFn : Val := .recE none (some "p") (.fieldLoad (.var "p") 1)
def tailFn : Val := .recE none (some "p") (.fieldLoad (.var "p") 2)
def isEmptyFn : Val := .recE none (some "p")
  (.ifE (.fieldLoad (.var "p") 0) (.val (flag false)) (.val (flag true)))
def reverseBody : Expr := .letE (some "nil") empty
  (.app (.val reverseAuxFn) (.struct [] [.var "p", .var "nil"]))
def reverseFn : Val := .recE none (some "p") reverseBody

end Cjr.LinkedList
