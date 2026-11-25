import Cjr.Execution

/-! Exact transition counts for the existing executable CJR small-step semantics.
One transition costs one unit, including a transition under any evaluation context.
This counts language reductions, not Lean interpreter instructions or native CPU cycles. -/
namespace Cjr

inductive StepsN : Nat → Expr → State → Expr → State → Prop where
  | refl : StepsN 0 e s e s
  | cons : Step e s e₁ s₁ → StepsN n e₁ s₁ e₂ s₂ → StepsN (n+1) e s e₂ s₂

namespace StepsN
 theorem forget (h : StepsN n e s e' t) : Steps e s e' t := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons h ih
 theorem one (h : Step e s e' t) : StepsN 1 e s e' t := .cons h .refl
 theorem trans (h : StepsN n e s e₁ t) (h' : StepsN m e₁ t e₂ u) : StepsN (n+m) e s e₂ u := by
  induction h with
  | refl => simpa using h'
  | cons hs _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using StepsN.cons hs (ih h')
 theorem under (k : CtxItem) (h : StepsN n e s e' t) :
    StepsN n (fillItem k e) s (fillItem k e') t := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .cons (step_under k hs) ih
end StepsN

abbrev Exec (n : Nat) (e : Expr) (s : State) (v : Val) (t : State) := StepsN n e s (.val v) t
namespace Exec
 theorem recost (h : Exec n e s v t) (hn : n=m) : Exec m e s v t := hn ▸ h
 theorem value (v : Val) (s : State) : Exec 0 (.val v) s v s := .refl
 theorem letE (ha : Exec n a s v t) (hb : Exec m (substBinder x v b) t w u) :
    Exec (n+(m+1)) (.letE x a b) s w u :=
  (ha.under (.letCtx x b)).trans (.cons (by rfl) hb)
 theorem if_true (hc : Exec n c s (.lit (.bool true)) t) (ha : Exec m a t v u) :
    Exec (n+(m+1)) (.ifE c a b) s v u :=
  (hc.under (.ifCtx a b)).trans (.cons (by rfl) ha)
 theorem if_false (hc : Exec n c s (.lit (.bool false)) t) (hb : Exec m b t v u) :
    Exec (n+(m+1)) (.ifE c a b) s v u :=
  (hc.under (.ifCtx a b)).trans (.cons (by rfl) hb)
 theorem field (ha : Exec n a s (.lit (.obj p)) t) (hv : t.obj.lookup (⟨p⟩,i) = some v) :
    Exec (n+1) (.fieldLoad a i) s v t := by
  apply StepsN.trans (ha.under (.fieldLoadCtx i))
  apply StepsN.one
  have hh : baseStep (.fieldLoad (.val (.lit (.obj p))) i) t = some (.val v,t) := by
    change (t.obj.lookup (⟨p⟩,i)).bind (fun v => some (Expr.val v,t)) = _
    rw [hv]; rfl
  simp only [Step,step,fillItem,decompose,hh]
  rfl
 theorem binop (ha : Exec n a s v₁ t) (hb : Exec m b t v₂ u)
    (hv : binOpEval op v₁ v₂ = some v) : Exec (n+(m+1)) (.binOp op a b) s v u := by
  apply StepsN.trans (ha.under (.binOpL op b))
  apply StepsN.trans (hb.under (.binOpR op v₁))
  apply StepsN.one
  have hh : baseStep (.binOp op (.val v₁) (.val v₂)) u = some (.val v,u) := by
    change (binOpEval op v₁ v₂).bind (fun v => some (Expr.val v,u)) = _
    rw [hv]; rfl
  simp only [Step,step,fillItem,decompose,hh]
  rfl
 theorem app_arg (fn : Val) (ha : Exec n a s v t) (hb : Exec m (.app (.val fn) (.val v)) t w u) :
    Exec (n+m) (.app (.val fn) a) s w u := (ha.under (.appR fn)).trans hb
 theorem struct_nil (vs : List Val) (s : State) : Exec 1 (.struct vs []) s (.struct vs) s :=
  StepsN.one (by rfl)
 theorem struct_cons (ha : Exec n a s v t) (hb : Exec m (.struct (vs ++ [v]) es) t w u) :
    Exec (n+(m+1)) (.struct vs (a :: es)) s w u :=
  (ha.under (.structCtx vs es)).trans (.cons (by rfl) hb)
 theorem new_nil (vs : List Val) (s : State) : Exec 1 (.new vs []) s (.lit (.obj s.next))
    {s with obj := (initFields s.next vs 0).union s.obj,next := s.next+1} := StepsN.one (by rfl)
 theorem new_cons (ha : Exec n a s v t) (hb : Exec m (.new (vs ++ [v]) es) t w u) :
    Exec (n+(m+1)) (.new vs (a :: es)) s w u :=
  (ha.under (.newCtx vs es)).trans (.cons (by rfl) hb)
 theorem struct_field (vs : List Val) (h : vs[i]? = some v) (s : State) :
    Exec 1 (.structLoad (.val (.struct vs)) i) s v s := by
  apply StepsN.one
  have hh : baseStep (.structLoad (.val (.struct vs)) i) s = some (.val v,s) := by
    change (vs[i]?).bind (fun v => some (Expr.val v,s)) = _
    rw [h]; rfl
  simp only [Step,step,decompose,hh]
  rfl
end Exec

/-- Determinism fixes both the transition count and terminal configuration. -/
theorem StepsN.terminal_unique (h : StepsN n e s finish t) :
    step finish t = none → ∀ m b u, StepsN m e s b u → step b u = none → n=m ∧ finish=b ∧ t=u := by
  induction h with
  | refl =>
    intro ha m b u h' hb
    cases h' with
    | refl => exact ⟨rfl,rfl,rfl⟩
    | cons hs _ => unfold Step at hs; rw [ha] at hs; contradiction
  | cons hs _ ih =>
    intro ha m b u h' hb
    cases h' with
    | refl => unfold Step at hs; rw [hb] at hs; contradiction
    | cons hs' ht' =>
      obtain ⟨rfl,rfl⟩ := step_deterministic hs hs'
      obtain ⟨hn,he,hu⟩ := ih ha _ _ _ ht' hb
      exact ⟨congrArg (·+1) hn,he,hu⟩

theorem exec_unique (h : Exec n e s v t) (h' : Exec m e s w u) : n=m ∧ v=w ∧ t=u := by
  obtain ⟨hn,hv,ht⟩ := h.terminal_unique (value_stuck _ _) _ _ _ h' (value_stuck _ _)
  exact ⟨hn,Expr.val.inj hv,ht⟩
@[simp] theorem run_value (fuel : Nat) (v : Val) (s : State) : run fuel (.val v) s = .done v s := by
  cases fuel <;> rfl

/-- A counted derivation supplies an exact sufficient fuel and any larger fuel. -/
theorem StepsN.run (h : StepsN n e s finish t) :
    ∀ v, toVal finish = some v → ∀ extra, run (n+extra) e s = .done v t := by
  induction h with
  | refl =>
    intro v hv extra
    have he := of_toVal hv
    rw [he]
    exact run_value _ _ _
  | @cons e s e₁ s₁ n e₂ t hs ht ih =>
    intro v hv extra
    have hn := step_nonvalue hs
    unfold Step at hs
    have heq : n+1+extra=(n+extra)+1 := by omega
    rw [heq]
    simp only [Cjr.run,hn,hs]
    exact ih v hv extra

theorem Exec.run (h : Exec n e s v t) (extra : Nat := 0) : run (n+extra) e s = .done v t :=
  StepsN.run h v rfl extra

end Cjr
