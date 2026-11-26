import Cjr

/-! Structural return-value safety for the actual CJR small-step semantics. -/
namespace Cjr

/-- A syntactic certificate that every completed execution returns a value in P.
Initializers and conditions may be arbitrary CJR programs with effects. -/
inductive ReturnsOnly (P : Val → Prop) : Expr → Prop where
  | value (h : P v) : ReturnsOnly P (.val v)
  | letE (h : ∀ v, ReturnsOnly P (substBinder x v body)) :
      ReturnsOnly P (.letE x init body)
  | ifE {guardCond a b : Expr} (yes : ReturnsOnly P a) (no : ReturnsOnly P b) :
      ReturnsOnly P (.ifE guardCond a b)

private theorem step_frame (k : CtxItem) (hn : toVal e = none) (s : State) :
    step (fillItem k e) s =
      (step e s).map (fun (e',t) => (fillItem k e',t)) := by
  unfold step
  rw [decompose_fillItem k e hn]
  cases hd : decompose e with
  | mk ks redex =>
    cases hb : baseStep redex s with
    | none => simp [descend,hb]
    | some result =>
      rcases result with ⟨e',t⟩
      simp [descend,hb,fill]

/-- Preservation of a return-value certificate across one concrete CJR step. -/
theorem ReturnsOnly.step (safe : ReturnsOnly P e) (hs : Step e s e' t) :
    ReturnsOnly P e' := by
  cases safe with
  | value h =>
    unfold Step at hs
    rw [value_stuck] at hs
    contradiction
  | @letE x body init h =>
    cases hv : toVal init with
    | some v =>
      have hi := of_toVal hv
      subst init
      have hh : Cjr.step (.letE x (.val v) body) s = some (substBinder x v body,s) := rfl
      unfold Step at hs
      rw [hh] at hs
      obtain ⟨rfl,rfl⟩ := Option.some.inj hs
      exact h v
    | none =>
      have hh := step_frame (.letCtx x body) hv s
      simp only [fillItem] at hh
      unfold Step at hs
      rw [hh] at hs
      cases hi : Cjr.step init s with
      | none => simp [hi] at hs
      | some result =>
        rcases result with ⟨init',u⟩
        simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hs
        obtain ⟨rfl,rfl⟩ := hs
        exact .letE h
  | @ifE cond a b ha hb =>
    cases hv : toVal cond with
    | some v =>
      have hc := of_toVal hv
      subst cond
      cases v with
      | lit l =>
        cases l with
        | bool flag =>
          cases flag with
          | false =>
            change some (b,s) = some (e',t) at hs
            obtain ⟨rfl,rfl⟩ := Option.some.inj hs
            exact hb
          | true =>
            change some (a,s) = some (e',t) at hs
            obtain ⟨rfl,rfl⟩ := Option.some.inj hs
            exact ha
        | _ => change none = some (e',t) at hs; contradiction
      | recE => change none = some (e',t) at hs; contradiction
      | struct => change none = some (e',t) at hs; contradiction
    | none =>
      have hh := step_frame (.ifCtx a b) hv s
      simp only [fillItem] at hh
      unfold Step at hs
      rw [hh] at hs
      cases hc : Cjr.step cond s with
      | none => simp [hc] at hs
      | some result =>
        rcases result with ⟨cond',u⟩
        simp only [hc,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hs
        obtain ⟨rfl,rfl⟩ := hs
        exact .ifE ha hb

theorem ReturnsOnly.steps (safe : ReturnsOnly P e) (he : Steps e s e' t) :
    ReturnsOnly P e' := by
  induction he with
  | refl => exact safe
  | cons hs _ ih => exact ih (safe.step hs)

/-- Soundness of the structural certificate for unbounded small-step execution.
This theorem asserts partial correctness, not termination. -/
theorem ReturnsOnly.sound (safe : ReturnsOnly P e) (he : Evaluates e s v t) : P v := by
  have terminal : ReturnsOnly P (.val v) := safe.steps he
  cases terminal with
  | value h => exact h

end Cjr
