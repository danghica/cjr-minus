import Anonymity

namespace Cjr.Voting

/-- PARETO EFFICIENCY (dominated-candidate exclusion): if every voter strictly
prefers valid candidate A to B in a nonempty electorate, no completed execution
of the checked CJR election can return B. Partial rankings treat omitted options
as below ranked ones. No bound on profiles or interpreter fuel is assumed. -/
theorem election_pareto (ha : a < n) (hu : UnanimouslyPrefers bs a b)
    (s t : State) : ¬ ElectionResult n bs s (.lit (.int b)) t := by
  rintro ⟨e,he,hrun⟩
  have hs := allowedValue_nat_member ((election_return_safe he).sound hrun)
  have hcanon : UnanimouslyPrefers (canonicalBallots bs) a b :=
    (unanimouslyPrefers_perm (canonicalBallots_perm bs).symm).mp hu
  exact paretoCandidates_excludes ha hcanon hs

theorem election_empty_no_winner (n b : Nat) (s t : State) :
    ¬ ElectionResult n [] s (.lit (.int b)) t := by
  rintro ⟨e,he,hrun⟩
  have hs := allowedValue_nat_member ((election_return_safe he).sound hrun)
  simp [paretoCandidates,canonicalBallots] at hs

/-- Literal universal-preference formulation, also covering an empty electorate:
there are no winners in that case, so the implication still holds. -/
theorem election_pareto_all_profiles (ha : a < n)
    (hu : ∀ row ∈ bs, Prefers row a b) (s t : State) :
    ¬ ElectionResult n bs s (.lit (.int b)) t := by
  by_cases hempty : bs = []
  · subst bs
    exact election_empty_no_winner n b s t
  · exact election_pareto ha ⟨hempty,hu⟩ s t

/-- Equivalent result-oriented formulation: any actual returned winner differs
from a unanimously dominated candidate. -/
theorem election_winner_not_dominated (ha : a < n)
    (hu : UnanimouslyPrefers bs a b) (hrun : ElectionResult n bs s winner t) :
    winner ≠ .lit (.int b) := by
  intro heq
  subst winner
  exact election_pareto ha hu s t hrun

/-- The property can be used directly with the executable interpreter; a completed
`run` is connected to the operational theorem by the existing soundness lemma. -/
theorem election_run_pareto (ha : a < n) (hu : UnanimouslyPrefers bs a b)
    (he : election n bs = .ok e) (fuel : Nat) (s t : State) :
    run fuel e s ≠ .done (.lit (.int b)) t := by
  intro hrun
  exact election_pareto ha hu s t ⟨e,he,run_done_steps hrun⟩

end Cjr.Voting
