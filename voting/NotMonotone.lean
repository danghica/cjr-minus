import Monotonicity

namespace Cjr.Voting
namespace MonotonicityCounterexample

theorem original_complete : CompleteProfile 3 original := by unfold CompleteProfile; decide
theorem raised_complete : CompleteProfile 3 raised := by unfold CompleteProfile; decide

/-- All candidates remain Pareto-eligible on both profiles. The guard does not
cause the winner change or substitute the no-winner sentinel. -/
theorem original_all_eligible : paretoCandidates 3 (canonicalBallots original) = [0,1,2] := by
  rw [original_canonical]
  decide

theorem raised_all_eligible : paretoCandidates 3 (canonicalBallots raised) = [0,1,2] := by
  rw [raised_canonical]
  decide

/-- Exactly the last voter raises candidate 0 from last to first, passing 2 and
1 in that order. All six other ballots, and all other relative orders, stay put. -/
theorem raises_winner : ProfileRaises 0 original raised := by
  have hlast : BallotRaises 0 [2,1,0] [0,2,1] := by
    exact ⟨by decide,[],[2,1],[],by decide,rfl,rfl⟩
  iterate 6 apply ProfileRaises.cons (.inl rfl)
  exact .cons (.inr hlast) .nil

/-- Extract an actual small-step execution from a successful observed interpreter
result, using the existing interpreter-soundness theorem. -/
theorem observed_sound (h : observed bs = some c) :
    ∃ t, ElectionResult 3 bs stateInit (.lit (.int c)) t := by
  unfold observed at h
  cases he : election 3 bs with
  | error err => simp [he] at h
  | ok e =>
    simp only [he] at h
    cases hr : run 20000 e stateInit with
    | stuck e' t => simp [hr] at h
    | timeout e' t => simp [hr] at h
    | done v t =>
      rw [hr] at h
      cases v with
      | recE => contradiction
      | struct => contradiction
      | lit l =>
        cases l with
        | int w =>
          have hw : w = c := Option.some.inj h
          subst w
          exact ⟨t,e,he,run_done_steps hr⟩
        | _ => contradiction

theorem original_wins : ∃ t, ElectionResult 3 original stateInit (.lit (.int 0)) t :=
  observed_sound original_observed

theorem raised_loses : ∃ t, ElectionResult 3 raised stateInit (.lit (.int 1)) t :=
  observed_sound raised_observed

private theorem result_unique (h : ElectionResult n bs s v t)
    (h' : ElectionResult n bs s w u) : v = w := by
  obtain ⟨e,he,hv⟩ := h
  obtain ⟨e',he',hw⟩ := h'
  have heq : e = e' := Except.ok.inj (he.symm.trans he')
  subst e'
  exact (evaluates_unique hv hw).1

theorem raised_cannot_win : ¬ ∃ t, ElectionResult 3 raised stateInit (.lit (.int 0)) t := by
  rintro ⟨t,ht⟩
  obtain ⟨u,hu⟩ := raised_loses
  have hbad := result_unique ht hu
  simp at hbad

end MonotonicityCounterexample

/-- The checked CJR election is NOT monotonic, even for complete strict rankings
and a change to a single voter. This is a countertheorem, not an assumed failure. -/
theorem election_not_monotone : ¬ Monotone := by
  intro hmono
  obtain ⟨t,ht⟩ := MonotonicityCounterexample.original_wins
  exact MonotonicityCounterexample.raised_cannot_win
    (hmono 3 0 _ _ t (by decide)
      MonotonicityCounterexample.original_complete
      MonotonicityCounterexample.raised_complete
      MonotonicityCounterexample.raises_winner ht)

end Cjr.Voting
