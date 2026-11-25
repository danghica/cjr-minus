import Cjr.LinkedList.Heap

namespace Cjr.LinkedList
open Evaluates

theorem empty_correct (s : State) :
    Evaluates empty s (reference s.next) (nodeState s false 0 (.lit .unit)) :=
  new_nil _ _

theorem cons_correct (s : State) (x : Int) (p : Loc) :
    Evaluates (cons x p) s (reference s.next) (nodeState s true x (reference p)) :=
  new_nil _ _

theorem head_correct (h : Represents s p (x :: xs)) : Evaluates (head p) s (.lit (.int x)) s := by
  cases h with
  | cons _ hv _ _ => exact field (value _ _) hv

theorem tail_correct (h : Represents s p (x :: xs)) :
    ∃ q, Evaluates (tail p) s (reference q) s ∧ Represents s q xs := by
  cases h with
  | cons _ _ hn ht => exact ⟨_,field (value _ _) hn,ht⟩

theorem isEmpty_correct (h : Represents s p xs) :
    Evaluates (isEmpty p) s (flag xs.isEmpty) s := by
  cases h with
  | nil hf => exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | cons hf _ _ _ => exact Evaluates.if_true (field (value _ _) hf) (value _ _)

def lengthBranch (p : Loc) : Expr :=
  .ifE (.fieldLoad (refExpr p) 0)
    (.binOp .plus (integer 1) (.app (.val lengthFn) (.fieldLoad (refExpr p) 2))) (integer 0)

theorem length_unfold (p : Loc) (s : State) : Step (length p) s (lengthBranch p) s := by rfl

/-- Total correctness for arbitrary finite represented lists. Reading length leaves
all four heaps and the allocation counter exactly unchanged. -/
theorem length_correct (h : Represents s p xs) :
    Evaluates (length p) s (.lit (.int (xs.length : Int))) s := by
  induction h with
  | nil hf =>
    apply Steps.cons (length_unfold _ _)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | @cons p x q xs hf hv hn ht ih =>
    apply Steps.cons (length_unfold _ _)
    apply Evaluates.if_true (field (value _ _) hf)
    apply binop (value _ _) (app_arg lengthFn (field (value _ _) hn) ih)
    change some (Val.lit (.int (1 + (xs.length : Int)))) = some (Val.lit (.int ((x :: xs).length : Int)))
    congr 3
    simp [Int.add_comm]

def appendBranch (p q : Loc) : Expr :=
  .ifE (.fieldLoad (refExpr p) 0)
    (.new [] [.val (flag true), .fieldLoad (refExpr p) 1,
      .app (.val appendFn) (.struct [] [.fieldLoad (refExpr p) 2, refExpr q])]) (refExpr q)

def reverseAuxBranch (p q : Loc) : Expr :=
  .ifE (.fieldLoad (refExpr p) 0)
    (.app (.val reverseAuxFn) (.struct [] [.fieldLoad (refExpr p) 2,
      .new [] [.val (flag true), .fieldLoad (refExpr p) 1, refExpr q]])) (refExpr q)

theorem append_unfold (p q : Loc) (s : State) : Steps (append p q) s (appendBranch p q) s := by
  apply Steps.cons (show Step (append p q) s
    (substBinder (some "args") (pair p q) (substBinder (some "append") appendFn appendBody)) s from rfl)
  apply steps_trans (steps_under (.letCtx (some "p") _) (struct_field _ (i := 0) (by rfl) s))
  apply Steps.cons (by rfl)
  apply steps_trans (steps_under (.letCtx (some "q") _) (struct_field _ (i := 1) (by rfl) s))
  exact .cons (by rfl) .refl

theorem reverseAux_unfold (p q : Loc) (s : State) :
    Steps (reverseAux p q) s (reverseAuxBranch p q) s := by
  apply Steps.cons (show Step (reverseAux p q) s
    (substBinder (some "args") (pair p q) (substBinder (some "reverseAux") reverseAuxFn reverseAuxBody)) s from rfl)
  apply steps_trans (steps_under (.letCtx (some "p") _) (struct_field _ (i := 0) (by rfl) s))
  apply Steps.cons (by rfl)
  apply steps_trans (steps_under (.letCtx (some "q") _) (struct_field _ (i := 1) (by rfl) s))
  exact .cons (by rfl) .refl

/-- Successful persistent operations preserve all caller-owned object cells and
leave stack/raw/block heaps unchanged. -/
structure Preserves (s t : State) : Prop where
  bounded : Bounded t
  extension : Extends s t
  frame : Frame s t

namespace Preserves
 theorem refl (hb : Bounded s) : Preserves s s := ⟨hb,extends_refl _,frame_refl _⟩
 theorem trans (h : Preserves s t) (h' : Preserves t u) : Preserves s u :=
  ⟨h'.bounded,extends_trans h.extension h'.extension,frame_trans h.frame h'.frame⟩
 theorem node (hb : Bounded s) : Preserves s (nodeState s tag x q) :=
  ⟨node_bounded hb,node_extends hb,node_frame _⟩
end Preserves

/-- Append copies the first spine and shares the second; input nodes remain valid. -/
theorem append_correct (hp : Represents s p xs) (hq : Represents s q ys) (hb : Bounded s) :
    ∃ r t, Evaluates (append p q) s (reference r) t ∧ Represents t r (xs ++ ys) ∧ Preserves s t := by
  induction hp generalizing q ys with
  | nil hf =>
    refine ⟨q,s,?_,hq,Preserves.refl hb⟩
    apply steps_trans (append_unfold _ _ _)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | @cons p x p' xs hf hv hn ht ih =>
    obtain ⟨r,t,he,hr,hpres⟩ := ih hq
    refine ⟨t.next,nodeState t true x (reference r),?_,cons_rep hr hpres.bounded,
      hpres.trans (Preserves.node hpres.bounded)⟩
    apply steps_trans (append_unfold _ _ _)
    apply Evaluates.if_true (field (value _ _) hf)
    apply new_cons (value _ _)
    apply new_cons (field (value _ _) hv)
    apply new_cons (app_arg appendFn ?_ he)
    · exact new_nil _ _
    · apply struct_cons (field (value _ _) hn)
      exact struct_cons (value _ _) (struct_nil _ _)

/-- Accumulator reverse implements reverse(xs) ++ ys and permits shared inputs. -/
theorem reverseAux_correct (hp : Represents s p xs) (hq : Represents s q ys) (hb : Bounded s) :
    ∃ r t, Evaluates (reverseAux p q) s (reference r) t ∧
      Represents t r (xs.reverse ++ ys) ∧ Preserves s t := by
  induction xs generalizing s p q ys with
  | nil =>
    obtain ⟨hf⟩ := hp
    refine ⟨q,s,?_,hq,Preserves.refl hb⟩
    apply steps_trans (reverseAux_unfold _ _ _)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | cons x xs ih =>
    cases hp with
    | @cons _ _ p' _ hf hv hn ht =>
      let u := nodeState s true x (reference q)
      have hu : Preserves s u := Preserves.node hb
      have hp' : Represents u p' xs := represents_mono ht hu.extension
      have hq' : Represents u s.next (x :: ys) := cons_rep hq hb
      obtain ⟨r,t,he,hr,hpres⟩ := ih hp' hq' hu.bounded
      refine ⟨r,t,?_,?_,hu.trans hpres⟩
      · apply steps_trans (reverseAux_unfold _ _ _)
        apply Evaluates.if_true (field (value _ _) hf)
        apply app_arg reverseAuxFn ?_ he
        apply struct_cons (field (value _ _) hn)
        apply struct_cons ?_ (struct_nil _ _)
        apply new_cons (value _ _)
        apply new_cons (field (value _ _) hv)
        exact new_cons (value _ _) (new_nil _ _)
      · simpa [List.reverse_cons, List.append_assoc] using hr

/-- Reverse allocates an empty sentinel and prepends into an accumulator. -/
theorem reverse_correct (hp : Represents s p xs) (hb : Bounded s) :
    ∃ r t, Evaluates (reverse p) s (reference r) t ∧ Represents t r xs.reverse ∧ Preserves s t := by
  let u := nodeState s false 0 (.lit .unit)
  have hu : Preserves s u := Preserves.node hb
  obtain ⟨r,t,he,hr,hpres⟩ := reverseAux_correct (represents_mono hp hu.extension) nil_rep hu.bounded
  refine ⟨r,t,?_,?_,hu.trans hpres⟩
  · apply Evaluates.letE (empty_correct s)
    apply app_arg reverseAuxFn ?_ he
    exact struct_cons (value _ _) (struct_cons (value _ _) (struct_nil _ _))
  · simpa using hr

/-- Construction also executes in CJR, including every allocation and let binding. -/
theorem ofList_correct (xs : List Int) (s : State) (hb : Bounded s) :
    ∃ p t, Evaluates (ofList xs) s (reference p) t ∧ Represents t p xs ∧ Preserves s t := by
  induction xs generalizing s with
  | nil => exact ⟨s.next,_,empty_correct s,nil_rep,Preserves.node hb⟩
  | cons x xs ih =>
    obtain ⟨p,t,he,hr,hpres⟩ := ih s hb
    refine ⟨t.next,nodeState t true x (reference p),?_,cons_rep hr hpres.bounded,
      hpres.trans (Preserves.node hpres.bounded)⟩
    apply Evaluates.letE he
    exact new_cons (value _ _) (new_cons (value _ _) (new_cons (value _ _) (new_nil _ _)))

/-- The exported constructor is an ordinary CJR function with a packed argument. -/
theorem consCall_correct (s : State) (x : Int) (p : Loc) :
    Evaluates (consCall x p) s (reference s.next) (nodeState s true x (reference p)) := by
  apply Steps.cons (show Step (consCall x p) s
    (substBinder (some "args") (.struct [.lit (.int x),reference p]) consBody) s from rfl)
  apply steps_trans (steps_under (.letCtx (some "x") _) (struct_field _ (i := 0) (by rfl) s))
  apply Steps.cons (by rfl)
  apply steps_trans (steps_under (.letCtx (some "xs") _) (struct_field _ (i := 1) (by rfl) s))
  apply Steps.cons (by rfl)
  exact new_cons (value _ _) (new_cons (value _ _) (new_cons (value _ _) (new_nil _ _)))

theorem headCall_correct (h : Represents s p (x :: xs)) :
    Evaluates (.app (.val headFn) (refExpr p)) s (.lit (.int x)) s :=
  .cons (by rfl) (head_correct h)

theorem tailCall_correct (h : Represents s p (x :: xs)) :
    ∃ q, Evaluates (.app (.val tailFn) (refExpr p)) s (reference q) s ∧ Represents s q xs := by
  obtain ⟨q,he,hr⟩ := tail_correct h
  exact ⟨q,.cons (by rfl) he,hr⟩

theorem isEmptyCall_correct (h : Represents s p xs) :
    Evaluates (.app (.val isEmptyFn) (refExpr p)) s (flag xs.isEmpty) s :=
  .cons (by rfl) (isEmpty_correct h)

theorem reverseCall_correct (hp : Represents s p xs) (hb : Bounded s) :
    ∃ r t, Evaluates (.app (.val reverseFn) (refExpr p)) s (reference r) t ∧
      Represents t r xs.reverse ∧ Preserves s t := by
  obtain ⟨r,t,he,hr,hpres⟩ := reverse_correct hp hb
  exact ⟨r,t,.cons (by rfl) he,hr,hpres⟩

end Cjr.LinkedList
