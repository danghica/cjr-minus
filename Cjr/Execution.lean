import Cjr.Properties

/-! Compositional rules proved for the executable small-step relation. -/
namespace Cjr

theorem step_nonvalue (h : Step e s e' s') : toVal e = none := by
  cases hv : toVal e with
  | none => rfl
  | some v =>
    have he := of_toVal hv
    subst e
    simp only [Step, value_stuck, reduceCtorEq] at h

theorem step_under (k : CtxItem) (h : Step e s e' s') :
    Step (fillItem k e) s (fillItem k e') s' := by
  have hd := decompose_fillItem k e (step_nonvalue h)
  unfold Step step at h ⊢
  rw [hd]
  cases he : decompose e with
  | mk ks r =>
    rw [he] at h
    cases hb : baseStep r s with
    | none => simp [hb] at h
    | some p =>
      rcases p with ⟨r',t⟩
      simp [hb] at h
      rcases h with ⟨rfl,rfl⟩
      simp [descend, hb, fill]

theorem steps_under (k : CtxItem) (h : Steps e s e' s') :
    Steps (fillItem k e) s (fillItem k e') s' := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons (step_under k h) ih

theorem steps_one (h : Step e s e' s') : Steps e s e' s' := .cons h .refl

/-- Terminating execution in the existing small-step semantics, without a fuel bound. -/
def Evaluates (e : Expr) (s : State) (v : Val) (t : State) : Prop := Steps e s (.val v) t

namespace Evaluates
 theorem value (v : Val) (s : State) : Evaluates (.val v) s v s := .refl
 theorem letE (h₁ : Evaluates a s v t)
    (h₂ : Evaluates (substBinder x v b) t w u) : Evaluates (.letE x a b) s w u := by
  apply steps_trans (steps_under (.letCtx x b) h₁)
  exact .cons (by rfl) h₂
 theorem if_true (h : Evaluates c s (.lit (.bool true)) t)
    (hb : Evaluates a t v u) : Evaluates (.ifE c a b) s v u := by
  apply steps_trans (steps_under (.ifCtx a b) h)
  exact .cons (by rfl) hb
 theorem if_false (h : Evaluates c s (.lit (.bool false)) t)
    (hb : Evaluates b t v u) : Evaluates (.ifE c a b) s v u := by
  apply steps_trans (steps_under (.ifCtx a b) h)
  exact .cons (by rfl) hb
 theorem field (h : Evaluates e s (.lit (.obj p)) t)
    (hv : t.obj.lookup (⟨p⟩,i) = some v) : Evaluates (.fieldLoad e i) s v t := by
  apply steps_trans (steps_under (.fieldLoadCtx i) h)
  apply steps_one
  have hh : baseStep (.fieldLoad (.val (.lit (.obj p))) i) t = some (.val v,t) := by
    change (t.obj.lookup (⟨p⟩,i)).bind (fun v => some (Expr.val v,t)) = _
    rw [hv]
    rfl
  simp only [Step, step, fillItem, decompose, hh]
  rfl
 theorem binop (h₁ : Evaluates a s v₁ t) (h₂ : Evaluates b t v₂ u)
    (hv : binOpEval op v₁ v₂ = some v) : Evaluates (.binOp op a b) s v u := by
  apply steps_trans (steps_under (.binOpL op b) h₁)
  apply steps_trans (steps_under (.binOpR op v₁) h₂)
  apply steps_one
  have hh : baseStep (.binOp op (.val v₁) (.val v₂)) u = some (.val v,u) := by
    change (binOpEval op v₁ v₂).bind (fun v => some (Expr.val v,u)) = _
    rw [hv]
    rfl
  simp only [Step, step, fillItem, decompose, hh]
  rfl
 theorem app (h₁ : Evaluates f s (.recE self arg body) t) (h₂ : Evaluates a t v u)
    (hb : Evaluates (substBinder arg v (substBinder self (.recE self arg body) body)) u w z) :
    Evaluates (.app f a) s w z := by
  apply steps_trans (steps_under (.appL a) h₁)
  apply steps_trans (steps_under (.appR (.recE self arg body)) h₂)
  exact .cons (by rfl) hb
 theorem app_arg (fn : Val) (ha : Evaluates a s v t)
    (hb : Evaluates (.app (.val fn) (.val v)) t w u) :
    Evaluates (.app (.val fn) a) s w u :=
  steps_trans (steps_under (.appR fn) ha) hb
 theorem struct_nil (vs : List Val) (s : State) : Evaluates (.struct vs []) s (.struct vs) s :=
  steps_one (by rfl)
 theorem struct_cons (ha : Evaluates a s v t)
    (hb : Evaluates (.struct (vs ++ [v]) es) t w u) :
    Evaluates (.struct vs (a :: es)) s w u := by
  apply steps_trans (steps_under (.structCtx vs es) ha)
  exact .cons (by rfl) hb
 theorem new_nil (vs : List Val) (s : State) : Evaluates (.new vs []) s (.lit (.obj s.next))
    {s with obj := (initFields s.next vs 0).union s.obj, next := s.next + 1} :=
  steps_one (by rfl)
 theorem new_cons (ha : Evaluates a s v t)
    (hb : Evaluates (.new (vs ++ [v]) es) t w u) :
    Evaluates (.new vs (a :: es)) s w u := by
  apply steps_trans (steps_under (.newCtx vs es) ha)
  exact .cons (by rfl) hb
 theorem struct_field (vs : List Val) (h : vs[i]? = some v) (s : State) :
    Evaluates (.structLoad (.val (.struct vs)) i) s v s := by
  apply steps_one
  have hh : baseStep (.structLoad (.val (.struct vs)) i) s = some (.val v,s) := by
    change (vs[i]?).bind (fun v => some (Expr.val v,s)) = _
    rw [h]
    rfl
  simp only [Step,step,decompose,hh]
  rfl

 theorem seq (ha : Evaluates a s v t) (hb : Evaluates b t w u) : Evaluates (.seq a b) s w u := by
  apply steps_trans (steps_under (.seqCtx b) ha)
  exact .cons (by rfl) hb
 theorem field_store (ha : Evaluates a s (.lit (.obj p)) t) (hb : Evaluates b t v u)
    (hc : u.obj.lookup (⟨p⟩,i) = some old) :
    Evaluates (.fieldStore a i b) s (.lit .unit) {u with obj := u.obj.insert (⟨p⟩,i) v} := by
  apply steps_trans (steps_under (.fieldStoreL i b) ha)
  apply steps_trans (steps_under (.fieldStoreR (.lit (.obj p)) i) hb)
  apply steps_one
  have hh : baseStep (.fieldStore (.val (.lit (.obj p))) i (.val v)) u =
      some (unitExpr,{u with obj := u.obj.insert (⟨p⟩,i) v}) := by
    change (u.obj.lookup (⟨p⟩,i)).bind (fun _ => some (unitExpr,{u with obj := u.obj.insert (⟨p⟩,i) v})) = _
    rw [hc]
    rfl
  simp only [Step,step,fillItem,decompose,hh]
  rfl

end Evaluates
/-- Any finite derivation ending in a value is reproduced by the fuelled interpreter
with some finite fuel. Together with `run_done_steps`, this connects both directions. -/
theorem steps_run (h : Steps e s e' t) (hv : toVal e' = some v) :
    ∃ fuel, run fuel e s = .done v t := by
  induction h with
  | refl =>
    refine ⟨0,?_⟩
    simp only [run,hv]
  | cons hs _ ih =>
    obtain ⟨fuel,hf⟩ := ih hv
    refine ⟨fuel+1,?_⟩
    have hn := step_nonvalue hs
    unfold Step at hs
    simp only [run,hn,hs]
    exact hf

theorem evaluates_run (h : Evaluates e s v t) : ∃ fuel, run fuel e s = .done v t :=
  steps_run h rfl

/-- Deterministic reduction has at most one terminal configuration. -/
theorem steps_terminal_unique (h : Steps e s a t) :
    step a t = none → ∀ b u, Steps e s b u → step b u = none → a = b ∧ t = u := by
  induction h with
  | refl =>
    intro ha b u h' hb
    cases h' with
    | refl => exact ⟨rfl,rfl⟩
    | cons hs _ => unfold Step at hs; rw [ha] at hs; contradiction
  | cons hs _ ih =>
    intro ha b u h' hb
    cases h' with
    | refl => unfold Step at hs; rw [hb] at hs; contradiction
    | cons hs' ht =>
      obtain ⟨rfl,rfl⟩ := step_deterministic hs hs'
      exact ih ha _ _ ht hb

theorem evaluates_unique (h : Evaluates e s v t) (h' : Evaluates e s w u) : v = w ∧ t = u := by
  obtain ⟨hv,ht⟩ := steps_terminal_unique h (value_stuck _ _) _ _ h' (value_stuck _ _)
  exact ⟨Expr.val.inj hv,ht⟩

end Cjr
