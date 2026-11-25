import Cjr.LinkedList.Correctness

namespace Cjr.LinkedList
open Evaluates

/-- A terminating computation returning a list with the specified contents and
preserving every pre-existing heap cell. This uses the executable `Steps` relation. -/
def Computes (s : State) (e : Expr) (xs : List Int) : Prop :=
  ∃ p t, Evaluates e s (reference p) t ∧ Represents t p xs ∧ Preserves s t

/-- A list expression implements a sequence in every bounded object-heap extension
of the initial state. Quantification over extensions permits sequential composition. -/
def Models (s : State) (e : Expr) (xs : List Int) : Prop :=
  ∀ t, Bounded t → Extends s t → Computes t e xs

/-- An integer-valued observation, also in all bounded heap extensions. -/
def Measures (s : State) (e : Expr) (n : Int) : Prop :=
  ∀ t, Bounded t → Extends s t → ∃ u, Evaluates e t (.lit (.int n)) u ∧ Preserves t u

/-- Source-level composition: the arguments are executed in CJR, not combined by Lean. -/
def appendExpr (a b : Expr) : Expr := .app (.val appendFn) (.struct [] [a,b])
def reverseExpr (a : Expr) : Expr := .app (.val reverseAuxFn) (.struct [] [a,empty])
def consExpr (x : Int) (a : Expr) : Expr := .new [] [.val (flag true),integer x,a]
def lengthExpr (a : Expr) : Expr := .app (.val lengthFn) a

theorem models_ref (h : Represents s p xs) : Models s (refExpr p) xs := by
  intro t hb he
  exact ⟨p,t,value _ _,represents_mono h he,Preserves.refl hb⟩

theorem models_empty : Models s empty [] := by
  intro t hb _
  exact ⟨t.next,_,empty_correct _,nil_rep,Preserves.node hb⟩

theorem models_ofList (xs : List Int) : Models s (ofList xs) xs :=
  fun t hb _ => ofList_correct xs t hb

theorem models_cons (ha : Models s a xs) : Models s (consExpr x a) (x :: xs) := by
  intro t hb he
  obtain ⟨p,u,ha,hr,hpres⟩ := ha t hb he
  refine ⟨u.next,nodeState u true x (reference p),?_,cons_rep hr hpres.bounded,
    hpres.trans (Preserves.node hpres.bounded)⟩
  exact new_cons (value _ _) (new_cons (value _ _) (new_cons ha (new_nil _ _)))

theorem models_append (ha : Models s a xs) (hb : Models s b ys) :
    Models s (appendExpr a b) (xs ++ ys) := by
  intro t ht he
  obtain ⟨p,u,hea,hpa,hpres₁⟩ := ha t ht he
  obtain ⟨q,v,heb,hqb,hpres₂⟩ := hb u hpres₁.bounded (extends_trans he hpres₁.extension)
  obtain ⟨r,w,hec,hr,hpres₃⟩ := append_correct (represents_mono hpa hpres₂.extension) hqb hpres₂.bounded
  refine ⟨r,w,?_,hr,hpres₁.trans (hpres₂.trans hpres₃)⟩
  apply app_arg appendFn ?_ hec
  exact struct_cons hea (struct_cons heb (struct_nil _ _))

theorem models_reverse (ha : Models s a xs) : Models s (reverseExpr a) xs.reverse := by
  intro t ht he
  obtain ⟨p,u,hea,hpa,hpres₁⟩ := ha t ht he
  let v := nodeState u false 0 (.lit .unit)
  have hpres₂ : Preserves u v := Preserves.node hpres₁.bounded
  obtain ⟨r,w,her,hr,hpres₃⟩ := reverseAux_correct (represents_mono hpa hpres₂.extension) nil_rep hpres₂.bounded
  refine ⟨r,w,?_,?_,hpres₁.trans (hpres₂.trans hpres₃)⟩
  · apply app_arg reverseAuxFn ?_ her
    exact struct_cons hea (struct_cons (empty_correct _) (struct_nil _ _))
  · simpa using hr

theorem measures_length (ha : Models s a xs) : Measures s (lengthExpr a) (xs.length : Int) := by
  intro t ht he
  obtain ⟨p,u,hea,hp,hpres⟩ := ha t ht he
  exact ⟨u,app_arg lengthFn hea (length_correct hp),hpres⟩

/-- Empty is the left identity for append, with equality of sequence observations. -/
theorem append_empty_left (ha : Models s a xs) : Models s (appendExpr empty a) xs :=
  models_append models_empty ha

theorem append_empty_right (ha : Models s a xs) : Models s (appendExpr a empty) xs := by
  simpa using models_append ha (models_empty (s := s))

/-- Both actual CJR programs terminate and represent the same sequence. Locations
and newly allocated spines may differ; this is equality through the abstraction. -/
theorem append_associative (ha : Models s a xs) (hb : Models s b ys) (hc : Models s c zs) :
    Models s (appendExpr (appendExpr a b) c) (xs ++ (ys ++ zs)) ∧
    Models s (appendExpr a (appendExpr b c)) (xs ++ (ys ++ zs)) := by
  exact ⟨by simpa [List.append_assoc] using models_append (models_append ha hb) hc,
    models_append ha (models_append hb hc)⟩

theorem reverse_empty : Models s (reverseExpr empty) [] := models_reverse models_empty

theorem reverse_involutive (ha : Models s a xs) : Models s (reverseExpr (reverseExpr a)) xs := by
  simpa using models_reverse (models_reverse ha)

theorem reverse_append (ha : Models s a xs) (hb : Models s b ys) :
    Models s (reverseExpr (appendExpr a b)) (ys.reverse ++ xs.reverse) ∧
    Models s (appendExpr (reverseExpr b) (reverseExpr a)) (ys.reverse ++ xs.reverse) := by
  exact ⟨by simpa using models_reverse (models_append ha hb),models_append (models_reverse hb) (models_reverse ha)⟩

theorem reverse_cons (ha : Models s a xs) :
    Models s (reverseExpr (consExpr x a)) (xs.reverse ++ [x]) ∧
    Models s (appendExpr (reverseExpr a) (consExpr x empty)) (xs.reverse ++ [x]) := by
  exact ⟨by simpa using models_reverse (models_cons ha),
    models_append (models_reverse ha) (models_cons models_empty)⟩

theorem length_empty : Measures s (lengthExpr empty) 0 := measures_length models_empty

theorem length_cons (ha : Models s a xs) :
    Measures s (lengthExpr (consExpr x a)) ((xs.length : Int) + 1) := by
  simpa using measures_length (models_cons ha)

theorem length_append (ha : Models s a xs) (hb : Models s b ys) :
    Measures s (lengthExpr (appendExpr a b)) ((xs.length : Int) + (ys.length : Int)) := by
  simpa using measures_length (models_append ha hb)

theorem length_reverse (ha : Models s a xs) :
    Measures s (lengthExpr (reverseExpr a)) (xs.length : Int) := by
  simpa using measures_length (models_reverse ha)

theorem head_cons (ha : Models s a xs) : Measures s (.fieldLoad (consExpr x a) 1) x := by
  intro t hb he
  obtain ⟨p,u,hea,hp,hpres⟩ := models_cons (x := x) ha t hb he
  cases hp with
  | cons _ hv _ _ => exact ⟨u,field hea hv,hpres⟩

theorem tail_cons (ha : Models s a xs) : Models s (.fieldLoad (consExpr x a) 2) xs := by
  intro t hb he
  obtain ⟨p,u,hea,hp,hpres⟩ := models_cons (x := x) ha t hb he
  cases hp with
  | cons _ _ hn ht => exact ⟨_,u,field hea hn,ht,hpres⟩

/-- A client may use the fuelled interpreter too: the general algebraic contracts
imply some finite fuel suffices, rather than assuming a fixed test bound. -/
theorem models_terminate (ha : Models s a xs) (hb : Bounded s) :
    ∃ fuel p t, run fuel a s = .done (reference p) t ∧ Represents t p xs ∧ Preserves s t := by
  obtain ⟨p,t,he,hp,hpres⟩ := ha s hb (extends_refl s)
  obtain ⟨fuel,hf⟩ := evaluates_run he
  exact ⟨fuel,p,t,hf,hp,hpres⟩

/-- The specification holds for every completed execution, by determinism. -/
theorem models_all_results (ha : Models s a xs) (hb : Bounded s)
    (he : Evaluates a s (reference p) t) : Represents t p xs ∧ Preserves s t := by
  obtain ⟨q,u,he',hq,hpres⟩ := ha s hb (extends_refl s)
  obtain ⟨hv,ht⟩ := evaluates_unique he' he
  have hp : q = p := by cases hv; rfl
  subst q; subst u
  exact ⟨hq,hpres⟩

/-- No finite maximal execution gets stuck: its terminal expression must be the
specified list value. In particular, head/tail/append/reverse never dereference a
missing field when their representation preconditions hold. -/
theorem models_no_stuck (ha : Models s a xs) (hb : Bounded s)
    (he : Steps a s e t) (hn : step e t = none) :
    ∃ p, e = .val (reference p) ∧ Represents t p xs ∧ Preserves s t := by
  obtain ⟨p,u,he',hp,hpres⟩ := ha s hb (extends_refl s)
  obtain ⟨heq,hs⟩ := steps_terminal_unique he' (value_stuck _ _) e t he hn
  subst e; subst u
  exact ⟨p,rfl,hp,hpres⟩

end Cjr.LinkedList
