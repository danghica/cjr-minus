import Voting

/-! Anonymity of the checked election entry point, stated over actual CJR−
small-step executions. No assumed refinement theorem, fuel limit, voter bound,
or distinct-ballot premise is used. See ANONYMITY.md for the proof boundary. -/
namespace Cjr.Voting

/-- A completed execution of the actual CJR program built from a voter profile.
States and values are those of Cjr.Semantics, not a mathematical voting model. -/
def ElectionResult (n : Nat) (bs : List (List Nat))
    (s : State) (winner : Val) (t : State) : Prop :=
  ∃ e, election n bs = .ok e ∧ Evaluates e s winner t

/-- Stronger than equal winners: arbitrary voter permutations compile to exactly
the same CJR expression. Validation errors are also permutation-invariant. -/
theorem election_program_anonymous (n : Nat) {bs cs : List (List Nat)}
    (h : bs.Perm cs) : election n bs = election n cs := by
  unfold election
  rw [canonicalBallots_eq_of_perm h]

/-- ANONYMITY: reordering voters preserves exactly the completed CJR executions,
including the returned value and final machine state, from any initial state.
This is an unbounded theorem over arbitrary profiles and permutations. -/
theorem election_anonymous (n : Nat) {bs cs : List (List Nat)}
    (h : bs.Perm cs) (s : State) (winner : Val) (t : State) :
    ElectionResult n bs s winner t ↔ ElectionResult n cs s winner t := by
  simp only [ElectionResult, election_program_anonymous n h]

/-- Comparing any two completed executions of permuted inputs gives equal values
and states. Determinism rules out a different result from the same CJR term. -/
theorem election_winners_equal (n : Nat) {bs cs : List (List Nat)}
    (h : bs.Perm cs)
    (hb : ElectionResult n bs s v t) (hc : ElectionResult n cs s w u) :
    v = w ∧ t = u := by
  obtain ⟨e,he,hv⟩ := hb
  obtain ⟨f,hf,hw⟩ := hc
  have hef : e = f := Except.ok.inj
    (he.symm.trans ((election_program_anonymous n h).trans hf))
  subst f
  exact evaluates_unique hv hw

/-- Every fuel-bounded interpreter observation agrees, including timeout and
stuckness. Thus the execution theorem is not relying on equal termination fuel. -/
theorem election_run_anonymous (n : Nat) {bs cs : List (List Nat)}
    (h : bs.Perm cs) (he : election n bs = .ok e) (hf : election n cs = .ok f)
    (fuel : Nat) (s : State) : run fuel e s = run fuel f s := by
  have hef : e = f := Except.ok.inj
    (he.symm.trans ((election_program_anonymous n h).trans hf))
  rw [hef]

/-- Two positions in an otherwise unchanged profile. `middle` can be arbitrarily
long or empty, so this is any transposition, not only adjacent voters. -/
theorem swap_ballots_perm (before middle suffix : List (List Nat)) (a b : List Nat) :
    (before ++ (a :: (middle ++ (b :: suffix)))).Perm
      (before ++ (b :: (middle ++ (a :: suffix)))) := by
  exact List.Perm.append_left before List.cons_append_cons_perm

/-- The requested two-voter swap property, directly over CJR execution results. -/
theorem election_swap_anonymous (n : Nat)
    (before middle suffix : List (List Nat)) (a b : List Nat)
    (s : State) (winner : Val) (t : State) :
    ElectionResult n (before ++ (a :: (middle ++ (b :: suffix)))) s winner t ↔
      ElectionResult n (before ++ (b :: (middle ++ (a :: suffix)))) s winner t :=
  election_anonymous n (swap_ballots_perm before middle suffix a b) s winner t

end Cjr.Voting
