import Cjr
open Cjr Cjr.LinkedList Cjr.LinkedList.MergeSort

private def check (label : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError ("Cost regression failed: " ++ label))

/-- Independent countTransitionsment: increment once per invocation of the actual Step
function that produces a successor; there are no algorithm-specific constants. -/
private def countTransitions : Nat → Expr → State → Nat → Except String (Nat × Val × State)
  | fuel,e,s,count =>
    match toVal e with
    | some v => .ok (count,v,s)
    | none => match fuel with
      | 0 => .error "exceeded the proved size-only budget"
      | fuel+1 => match step e s with
        | none => .error "stuck"
        | some (e',s') => countTransitions fuel e' s' (count+1)

private def inputs : Nat → List (List Int)
  | 0 => [[]]
  | n+1 => (inputs n).flatMap (fun xs => [-1,0,1].map (· :: xs))

private def test (xs : List Int) : IO Nat := do
  let .done (.lit (.obj p)) s := run 1000000 (ofList xs) stateInit
    | throw (IO.userError "input construction failed")
  let .ok (count,_,_) := countTransitions (worstBudget xs.length) (sortList p) s 0
    | throw (IO.userError s!"budget failed for size {xs.length}")
  check "exact transition model" (count == sortSteps xs)
  check "upper budget" (count ≤ worstBudget xs.length)
  check "lower logarithmic bound" (15*xs.length*xs.length.log2 ≤ count)
  if xs.length ≥ 2 then
    check "Theta upper bound" (count ≤ 111*xs.length*xs.length.log2)
  let .ok (splitCount,_,_) := countTransitions (splitSteps xs.length) (splitList p) s 0
    | throw (IO.userError "split budget failed")
  check "exact split formula" (splitCount == 15*xs.length+6)
  return count

def main : IO Unit := do
  let exhaustive := (List.range 6).flatMap inputs
  for xs in exhaustive do let _ ← test xs
  for xs in ([List.replicate 32 0, (List.range 32).map (fun n => (31-n : Nat)),
    [9,-7,9,0,2,-3,8,1,-1,7,0,0]] : List (List Int)) do
    let _ ← test xs
  check "empty exact" (sortSteps [] == 3)
  check "singleton exact" (sortSteps [1] == 7)
  check "two ascending exact" (sortSteps [1,2] == 94)
  check "two descending exact" (sortSteps [2,1] == 96)
  check "budget n=1000" (worstBudget 1000 == 406970)
  check "budget n=1000000" (worstBudget 1000000 == 776999970)
  for n in List.range 1025 do
    check "ceil binary log power bound" (n ≤ 2^(ceilLog n))
    if n > 0 then
      check "minimal ceiling log" (ceilLog n == 0 || 2^(ceilLog n-1) < n)
  IO.println s!"Cost checks passed: {exhaustive.length} exhaustive inputs plus larger cases; exact Step counts, split constants, logarithmic bounds, budgets, and ceiling-log boundaries."
