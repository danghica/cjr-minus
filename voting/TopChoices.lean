import Pareto

namespace Cjr.Voting
open Cjr.Cangjie

private def num (n : Int) : Expr := .val (.lit (.int n))
private def v := Expr.var
private def op := Expr.binOp
private def unit : Expr := .val (.lit .unit)
private def seq (es : List Expr) (last : Expr := unit) := es.foldr Expr.seq last
private def vars (xs : List (String × Expr)) (body : Expr) :=
  xs.foldr (fun (x,e) b => Expr.varBind x e b) body
private def bindArgs (names : List String) (body : Expr) :=
  names.zipIdx.foldr (fun (x,i) b => Expr.letE (some x) (.structLoad (v "args") i) b) body
private def read (p : String) (i : Expr) := Expr.load (.offset (v p) i)
private def write (p : String) (i e : Expr) := Expr.store (.offset (v p) i) e
private def inc (x : String) := Expr.assign x (op .plus (v x) (num 1))
private def loop (i : String) (limit body : Expr) :=
  Expr.varBind i (num 0) (.whileE (op .le (v i) (op .minus limit (num 1))) (seq [body,inc i]))
private def call (fn : Val) (args : List Expr) := Expr.app (.val fn) (.struct [] args)

/-- Runtime counterpart of the checked single-winner Pareto guard, applied to
the residual rankings at each selection. Missing IDs have rank `width`. -/
def eligibleBody : Expr := bindArgs ["n","m","width","ballots","winner"]
  (vars [("safe",num 1)]
    (seq [loop "other" (v "n")
      (vars [("allPrefer",num 1)]
        (seq [loop "voter" (v "m")
          (vars [("otherRank",v "width"),("winnerRank",v "width")]
            (seq [loop "rank" (v "width")
              (.letE (some "entry") (read "ballots" (op .plus (op .mul (v "voter") (v "width")) (v "rank")))
                (seq [
                  .ifE (op .eq (v "entry") (v "other")) (.assign "otherRank" (v "rank")) unit,
                  .ifE (op .eq (v "entry") (v "winner")) (.assign "winnerRank" (v "rank")) unit])),
              .ifE (op .le (op .plus (v "otherRank") (num 1)) (v "winnerRank"))
                unit (.assign "allPrefer" (num 0))])),
          .ifE (op .eq (v "allPrefer") (num 1)) (.assign "safe" (num 0)) unit]))]
      (v "safe")))

def eligibleFn : Val := .recE none (some "args") eligibleBody

/-- Sequential IRV: count, emit, remove the selected ID everywhere, repeat.
Input memory is copied and left untouched. Caller supplies `limit` output cells;
the returned integer is the number written. Dimensions and limit are nonnegative.
Stop early at exhausted ballots or a rejected result. -/
def topIntoBody : Expr := bindArgs ["n","m","width","ballots","limit","output"]
  (.letE (some "cells") (op .mul (v "m") (v "width"))
  (.letE (some "scratch") (.alloc (.ifE (op .le (v "cells") (num 0)) (num 1) (v "cells")))
  (vars [("selected",num 0),("running",num 1)]
    (seq [loop "copyIndex" (v "cells") (write "scratch" (v "copyIndex") (read "ballots" (v "copyIndex"))),
      .whileE (op .and (op .eq (v "running") (num 1))
        (op .le (op .plus (v "selected") (num 1)) (v "limit")))
        (.letE (some "winner") (call votingFn [v "n",v "m",v "width",v "scratch"])
          (.ifE (op .le (v "winner") (num (-1))) (.assign "running" (num 0))
            (.ifE (op .eq (call eligibleFn [v "n",v "m",v "width",v "scratch",v "winner"]) (num 0))
              (.assign "running" (num 0))
              (seq [write "output" (v "selected") (v "winner"),inc "selected",
                loop "removeIndex" (v "cells")
                  (.ifE (op .eq (read "scratch" (v "removeIndex")) (v "winner"))
                    (write "scratch" (v "removeIndex") (num (-1))) unit)])))),
      .free (v "scratch")] (v "selected")))))

def topIntoFn : Val := .recE none (some "args") topIntoBody

/-- Return an owned ListNode chain in selection order. The raw output buffer is
freed before returning. The requested count may be zero. -/
def topBody : Expr := bindArgs ["n","m","width","ballots","limit"]
  (.letE (some "output") (.alloc (.ifE (op .le (v "limit") (num 0)) (num 1) (v "limit")))
  (.letE (some "count") (call topIntoFn [v "n",v "m",v "width",v "ballots",v "limit",v "output"])
  (vars [("result",.new [.lit (.bool false),.lit (.int 0),.lit .unit] []),
         ("resultIndex",op .minus (v "count") (num 1))]
    (seq [.whileE (op .le (num 0) (v "resultIndex"))
      (seq [.assign "result" (.new [] [.val (.lit (.bool true)),read "output" (v "resultIndex"),v "result"]),
        .assign "resultIndex" (op .minus (v "resultIndex") (num 1))]),
      .free (v "output")] (v "result")))))

def topFn : Val := .recE none (some "args") topBody

private def buildTopElection (n limit : Nat) (bs : List (List Nat)) : Except String Expr := do
  if limit > n then throw "requested choices exceed candidate count"
  -- Reuse existing validation; its single-winner expression is not executed here.
  let _ ← election n bs
  let width := bs.foldl (fun w row => max w row.length) 0
  let cells := bs.flatMap (fun row => row.map Int.ofNat ++ List.replicate (width-row.length) (-1))
  let stores := cells.zipIdx.map (fun (x,i) => write "matrix" (num i) (num x))
  return .letE (some "matrix") (.alloc (num (max 1 cells.length)))
    (seq stores (.letE (some "choices")
      (call topFn [num n,num bs.length,num width,v "matrix",num limit])
      (.seq (.free (v "matrix")) (v "choices"))))

def topElection (n limit : Nat) (bs : List (List Nat)) : Except String Expr :=
  buildTopElection n limit (canonicalBallots bs)

def topProgram (main : Expr) : Prog := {
  program main with
  classes := [Cjr.LinkedList.nodeDecl]
  fns := (program main).fns ++ [
    {name := "paretoEligible",arg := some "args",body := eligibleBody,
      tys := ["Int64","Int64","Int64","CPointer<Int64>","Int64"],ret := "Int64"},
    {name := "rankedChoicesInto",arg := some "args",body := topIntoBody,
      tys := ["Int64","Int64","Int64","CPointer<Int64>","Int64","CPointer<Int64>"],ret := "Int64"},
    {name := "rankedChoices",arg := some "args",body := topBody,
      tys := ["Int64","Int64","Int64","CPointer<Int64>","Int64"],ret := "ListNode"}]
}

/-- Voter anonymity holds for every user-supplied selection limit, including
validation and the actual multi-choice CJR expression. -/
theorem topElection_program_anonymous (n limit : Nat) (h : bs.Perm cs) :
    topElection n limit bs = topElection n limit cs := by
  unfold topElection
  rw [canonicalBallots_eq_of_perm h]

def TopElectionResult (n limit : Nat) (bs : List (List Nat))
    (s : State) (result : Val) (t : State) : Prop :=
  ∃ e, topElection n limit bs = .ok e ∧ Evaluates e s result t

theorem topElection_anonymous (n limit : Nat) (h : bs.Perm cs)
    (s : State) (result : Val) (t : State) :
    TopElectionResult n limit bs s result t ↔ TopElectionResult n limit cs s result t := by
  simp only [TopElectionResult,topElection_program_anonymous n limit h]

theorem topElection_run_anonymous (n limit : Nat) (h : bs.Perm cs)
    (he : topElection n limit bs = .ok e) (hf : topElection n limit cs = .ok f)
    (fuel : Nat) (s : State) : run fuel e s = run fuel f s := by
  have hef : e = f := Except.ok.inj (he.symm.trans ((topElection_program_anonymous n limit h).trans hf))
  rw [hef]

end Cjr.Voting
