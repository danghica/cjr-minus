import Cjr.Semantics
namespace Cjr

theorem decompose_fill (e : Expr) : fill (decompose e).1 (decompose e).2 = e := by
  fun_induction decompose e <;> simp_all [descend, fill, fillItem]

theorem baseStep_nonvalue (h : BaseStep e s e' s') : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some v =>
    have he := of_toVal hv
    subst e
    exact nomatch h

theorem decompose_fillItem (k : CtxItem) (e : Expr) (h : toVal e = none) :
    decompose (fillItem k e) = descend k (decompose e) := by
  cases k <;> cases e <;> simp_all only [toVal, Option.some_ne_none, fillItem, decompose, descend]

theorem contextual_fill (ks : List CtxItem) (h : ContextualStep e s e' s') :
    ContextualStep (fill ks e) s (fill ks e') s' := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact .under k ih

theorem step_contextual (h : Step e s e' s') : ContextualStep e s e' s' := by
  unfold Step step at h
  generalize hd : decompose e = d at h
  rcases d with ⟨ks, r⟩
  cases hb : baseStep r s with
  | none => simp [hb] at h
  | some p =>
    rcases p with ⟨r', t⟩
    simp [hb] at h
    rcases h with ⟨rfl, rfl⟩
    have hf := decompose_fill e
    rw [hd] at hf
    rw [← hf]
    exact contextual_fill ks (.head hb)

theorem steps_trans (h : Steps e s e₁ s₁) (h' : Steps e₁ s₁ e₂ s₂) : Steps e s e₂ s₂ := by
  induction h with
  | refl => exact h'
  | cons h _ ih => exact .cons h (ih h')

theorem run_done_steps {fuel : Nat} {e : Expr} {s : State} {v : Val} {t : State}
    (h : run fuel e s = .done v t) : Steps e s (.val v) t := by
  induction fuel generalizing e s with
  | zero =>
    cases hv : toVal e with
    | none => simp [run, hv] at h
    | some w =>
      simp [run, hv] at h
      rcases h with ⟨rfl, rfl⟩
      rw [of_toVal hv]
      exact .refl
  | succ fuel ih =>
    cases hv : toVal e with
    | some w =>
      simp [run, hv] at h
      rcases h with ⟨rfl, rfl⟩
      rw [of_toVal hv]
      exact .refl
    | none =>
      cases hs : step e s with
      | none => simp [run, hv, hs] at h
      | some p =>
        rcases p with ⟨e', s'⟩
        simp [run, hv, hs] at h
        exact .cons hs (ih h)

/-- Reflexive transitive closure of the independent contextual relation. -/
inductive ContextualSteps : Expr → State → Expr → State → Prop where
  | refl : ContextualSteps e s e s
  | cons : ContextualStep e s e₁ s₁ → ContextualSteps e₁ s₁ e₂ s₂ → ContextualSteps e s e₂ s₂

theorem steps_contextual (h : Steps e s e' s') : ContextualSteps e s e' s' := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons (step_contextual h) ih

/-- Every completed interpreter execution has a contextual reduction derivation. -/
theorem run_done_contextual {fuel : Nat} {e : Expr} {s : State} {v : Val} {t : State}
    (h : run fuel e s = .done v t) : ContextualSteps e s (.val v) t :=
  steps_contextual (run_done_steps h)
end Cjr
