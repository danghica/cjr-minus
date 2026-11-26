import Cjr
import Canonical
import ParetoGuard

/-! Single-winner instant runoff, implemented as CJR− expressions, not a Lean
replacement for execution. Candidate IDs are 0 .. n-1; -1 pads ballot rows. -/
namespace Cjr.Voting
open Cjr.Cangjie

private def num (n : Int) : Expr := .val (.lit (.int n))
private def v := Expr.var
private def add := Expr.binOp .plus
private def sub := Expr.binOp .minus
private def mul := Expr.binOp .mul
private def le := Expr.binOp .le
private def eq := Expr.binOp .eq
private def both := Expr.binOp .and
private def read (p : String) (i : Expr) := Expr.load (.offset (v p) i)
private def write (p : String) (i x : Expr) := Expr.store (.offset (v p) i) x
private def unit : Expr := .val (.lit .unit)
private def seq (es : List Expr) (last : Expr := unit) := es.foldr Expr.seq last
private def inc (x : String) := Expr.assign x (add (v x) (num 1))
private def vars (xs : List (String × Expr)) (body : Expr) :=
  xs.foldr (fun (x,e) b => Expr.varBind x e b) body
private def loop (i : String) (limit body : Expr) :=
  Expr.varBind i (num 0) (.whileE (le (v i) (sub limit (num 1))) (seq [body,inc i]))

/-- Arguments: candidate count, ballot count, row width, read-only ballot matrix.
Requires n > 0, m >= 0, width >= 0 and m*width readable cells. Rows contain
distinct valid IDs followed by -1 padding. See `election` for checked construction.
Returns -1 when no ballots remain; tied minima eliminate the greatest ID. -/
def body : Expr :=
  ["n","m","width","ballots"].zipIdx.foldr
    (fun (x,i) b => .letE (some x) (.structLoad (v "args") i) b)
    (.ifE (le (v "n") (num 0)) (num (-1))
      (.letE (some "active") (.alloc (v "n"))
      (.letE (some "counts") (.alloc (v "n"))
      (vars [("answer",num (-1)),("running",num 1)]
        (seq [
          loop "c" (v "n") (write "active" (v "c") (num 1)),
          .whileE (eq (v "running") (num 1))
            (vars [("total",num 0),("best",num (-1)),("bestVotes",num (-1)),
                   ("worst",num (-1)),("worstVotes",add (v "m") (num 1))]
              (seq [
                loop "reset" (v "n") (write "counts" (v "reset") (num 0)),
                loop "b" (v "m")
                  (vars [("r",num 0),("choice",num (-1))]
                    (seq [
                      .whileE (both (eq (v "choice") (num (-1)))
                        (le (v "r") (sub (v "width") (num 1))))
                        (.letE (some "candidate")
                          (read "ballots" (add (mul (v "b") (v "width")) (v "r")))
                          (seq [
                            -- Bounds check precedes indexing: CJR conjunction is strict.
                            .ifE (both (le (num 0) (v "candidate"))
                              (le (v "candidate") (sub (v "n") (num 1))))
                              (.ifE (eq (read "active" (v "candidate")) (num 1))
                                (.assign "choice" (v "candidate")) unit) unit,
                            inc "r"])),
                      .ifE (le (num 0) (v "choice"))
                        (seq [write "counts" (v "choice")
                          (add (read "counts" (v "choice")) (num 1)),inc "total"]) unit])),
                loop "c" (v "n")
                  (.ifE (eq (read "active" (v "c")) (num 1))
                    (.letE (some "votes") (read "counts" (v "c"))
                      (seq [
                        .ifE (le (add (v "bestVotes") (num 1)) (v "votes"))
                          (seq [.assign "best" (v "c"),.assign "bestVotes" (v "votes")]) unit,
                        .ifE (le (v "votes") (v "worstVotes"))
                          (seq [.assign "worst" (v "c"),.assign "worstVotes" (v "votes")]) unit])) unit),
                .ifE (eq (v "total") (num 0)) (.assign "running" (num 0))
                  (.ifE (le (add (v "total") (num 1)) (mul (num 2) (v "bestVotes")))
                    (seq [.assign "answer" (v "best"),.assign "running" (num 0)])
                    (write "active" (v "worst") (num 0)))])),
          .free (v "counts"),.free (v "active")] (v "answer"))))))

def votingFn : Val := .recE none (some "args") body

/-- Internal matrix builder, given a profile already in canonical voter order. -/
private def buildElection (n : Nat) (ballots : List (List Nat)) : Except String Expr := do
  for row in ballots do
    if row.any (· >= n) then throw "candidate ID out of range"
    if row.eraseDups.length != row.length then throw "duplicate candidate in ballot"
  if n == 0 then return num (-1)
  let width := ballots.foldl (fun a r => max a r.length) 0
  let cells := ballots.flatMap (fun row =>
    row.map Int.ofNat ++ List.replicate (width-row.length) (-1))
  let stores := cells.zipIdx.map (fun (x,i) => write "matrix" (num i) (num x))
  return .letE (some "matrix") (.alloc (num (max 1 cells.length)))
    (seq stores (.letE (some "result")
      (.app (.val votingFn) (.struct [] [num n,num ballots.length,num width,v "matrix"]))
      (.seq (.free (v "matrix")) (v "result"))))

/-- Validate a profile and construct its CJR program, owning and freeing the input
matrix. Canonical voter order makes anonymity hold at the program level.
Only whole ballots are reordered; rankings and multiplicities are preserved.
A CJR return-value guard excludes unanimously dominated winners. -/
def election (n : Nat) (ballots : List (List Nat)) : Except String Expr :=
  (buildElection n (canonicalBallots ballots)).map
    (paretoGuard n (canonicalBallots ballots))

/-- Structural return-value certificate for the actual compiled election. -/
theorem election_return_safe (he : election n bs = .ok e) :
    ReturnsOnly (AllowedValue (paretoCandidates n (canonicalBallots bs))) e := by
  unfold election at he
  cases hc : buildElection n (canonicalBallots bs) with
  | error error => simp [hc,Except.map] at he
  | ok core =>
    simp [hc,Except.map] at he
    subst e
    exact paretoGuard_safe _ _ _

def program (main : Expr) : Prog := {
  fns := [{name := "rankedChoice",arg := some "args",body := body,
           tys := ["Int64","Int64","Int64","CPointer<Int64>"],ret := "Int64"}]
  main := main
}
end Cjr.Voting
