import Cjr.LinkedList.Algebra
import Cjr.LinkedList.MergeSort.Math

namespace Cjr.LinkedList.MergeSort

def splitCore (recur p : Expr) : Expr :=
  .ifE (.fieldLoad p 0)
    (.letE (some "parts") (.app recur (.fieldLoad p 2))
      (.struct [] [
        .new [] [.val (flag true),.fieldLoad p 1,.structLoad (.var "parts") 1],
        .structLoad (.var "parts") 0]))
    (.struct [] [p,p])
def splitBody : Expr := splitCore (.var "splitList") (.var "p")
def splitFn : Val := .recE (some "splitList") (some "p") splitBody
def splitList (p : Loc) : Expr := .app (.val splitFn) (refExpr p)

def mergeCore (recur p q : Expr) : Expr :=
  .ifE (.fieldLoad p 0)
    (.ifE (.fieldLoad q 0)
      (.ifE (.binOp .le (.fieldLoad p 1) (.fieldLoad q 1))
        (.new [] [.val (flag true),.fieldLoad p 1,
          .app recur (.struct [] [.fieldLoad p 2,q])])
        (.new [] [.val (flag true),.fieldLoad q 1,
          .app recur (.struct [] [p,.fieldLoad q 2])]))
      p)
    q
def mergeBody : Expr :=
  .letE (some "p") (.structLoad (.var "args") 0)
    (.letE (some "q") (.structLoad (.var "args") 1)
      (mergeCore (.var "mergeLists") (.var "p") (.var "q")))
def mergeFn : Val := .recE (some "mergeLists") (some "args") mergeBody
def mergeList (p q : Loc) : Expr := .app (.val mergeFn) (.val (pair p q))

def sortCore (recur p : Expr) : Expr :=
  .ifE (.fieldLoad p 0)
    (.letE (some "t") (.fieldLoad p 2)
      (.ifE (.fieldLoad (.var "t") 0)
        (.letE (some "halves") (.app (.val splitFn) p)
          (.letE (some "left") (.app recur (.structLoad (.var "halves") 0))
            (.letE (some "right") (.app recur (.structLoad (.var "halves") 1))
              (.app (.val mergeFn) (.struct [] [.var "left",.var "right"])))))
        p))
    p
def sortBody : Expr := sortCore (.var "mergeSort") (.var "p")
def sortFn : Val := .recE (some "mergeSort") (some "p") sortBody
def sortList (p : Loc) : Expr := .app (.val sortFn) (refExpr p)
def sortExpr (e : Expr) : Expr := .app (.val sortFn) e

end Cjr.LinkedList.MergeSort
