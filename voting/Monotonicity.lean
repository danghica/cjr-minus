import Pareto

namespace Cjr.Voting

/-- Move C strictly upward across a nonempty segment, preserving the order of
every other candidate. The original ranking must have no duplicate IDs. -/
def BallotRaises (c : Nat) (old new : List Nat) : Prop :=
  old.Nodup ∧ ∃ before passed after : List Nat,
    passed ≠ [] ∧
    old = before ++ passed ++ (c :: after) ∧
    new = before ++ (c :: (passed ++ after))

/-- Each voter either leaves their ballot unchanged or raises the same C. -/
inductive ProfileRaises (c : Nat) : List (List Nat) → List (List Nat) → Prop where
  | nil : ProfileRaises c [] []
  | cons (change : old = new ∨ BallotRaises c old new)
      (rest : ProfileRaises c bs cs) : ProfileRaises c (old :: bs) (new :: cs)

/-- Complete, strict rankings of exactly the registered candidates. -/
def CompleteProfile (n : Nat) (bs : List (List Nat)) : Prop :=
  ∀ row ∈ bs, row.Perm (List.range n)

/-- Monotonicity, stated for actual completed executions of the checked program.
Even restricting inputs to complete strict rankings, this property is false. -/
def Monotone : Prop :=
  ∀ (n c : Nat) (bs cs : List (List Nat)) (t : State),
    c < n → CompleteProfile n bs → CompleteProfile n cs → ProfileRaises c bs cs →
    ElectionResult n bs stateInit (.lit (.int c)) t →
    ∃ u, ElectionResult n cs stateInit (.lit (.int c)) u

namespace MonotonicityCounterexample

def original : List (List Nat) :=
  [[0,1,2],[0,1,2],[1,0,2],[1,0,2],[2,1,0],[2,1,0],[2,1,0]]

def raised : List (List Nat) :=
  [[0,1,2],[0,1,2],[1,0,2],[1,0,2],[2,1,0],[2,1,0],[0,2,1]]

def raisedSorted : List (List Nat) :=
  [[0,1,2],[0,1,2],[0,2,1],[1,0,2],[1,0,2],[2,1,0],[2,1,0]]

theorem original_canonical : canonicalBallots original = original := by
  apply List.mergeSort_of_sorted
  decide

theorem raised_canonical : canonicalBallots raised = raisedSorted := by
  have hp : raised.Perm raisedSorted := by decide
  rw [canonicalBallots_eq_of_perm hp]
  apply List.mergeSort_of_sorted
  decide

def observed (bs : List (List Nat)) : Option Int :=
  match election 3 bs with
  | .error _ => none
  | .ok e => match run 20000 e stateInit with
    | .done (.lit (.int c)) _ => some c
    | _ => none

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
 theorem original_observed : observed original = some 0 := by
  unfold observed election
  rw [original_canonical]
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
 theorem raised_observed : observed raised = some 1 := by
  unfold observed election
  rw [raised_canonical]
  decide +kernel

end MonotonicityCounterexample
end Cjr.Voting
