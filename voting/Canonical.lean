import Std

namespace Cjr.Voting

/-- Canonicalize voter order only. A ballot's preference order is never changed.
Lexicographic sorting retains duplicate ballots with their full multiplicity. -/
def canonicalBallots (bs : List (List Nat)) : List (List Nat) :=
  bs.mergeSort (fun a b => decide (a ≤ b))

/-- Normalization neither adds nor removes voters, nor changes their rankings. -/
theorem canonicalBallots_perm (bs : List (List Nat)) :
    (canonicalBallots bs).Perm bs :=
  List.mergeSort_perm _ _

private theorem canonicalBallots_sorted (bs : List (List Nat)) :
    (canonicalBallots bs).Pairwise (fun a b => a ≤ b) := by
  have h := List.sorted_mergeSort
    (le := fun a b : List Nat => decide (a ≤ b))
    (fun a b c hab hbc => by
      simpa using List.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (fun a b => by
      rcases List.le_total a b with h | h <;> simp [h]) bs
  simpa only [decide_eq_true_eq] using h

/-- Any voter permutation produces the same canonical sequence, not merely the
same set of ballots. This includes profiles with repeated and empty ballots. -/
theorem canonicalBallots_eq_of_perm {bs cs : List (List Nat)} (h : bs.Perm cs) :
    canonicalBallots bs = canonicalBallots cs := by
  apply List.Perm.eq_of_sorted (le := fun a b : List Nat => a ≤ b)
    (fun a b _ _ hab hba => List.le_antisymm hab hba)
    (canonicalBallots_sorted bs) (canonicalBallots_sorted cs)
  exact (canonicalBallots_perm bs).trans (h.trans (canonicalBallots_perm cs).symm)

end Cjr.Voting
