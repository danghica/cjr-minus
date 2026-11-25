import Cjr.LinkedList.MergeSort.Code
namespace Cjr.LinkedList.MergeSort
open Evaluates

theorem split_unfold (p : Loc) (s : State) :
    Step (splitList p) s (splitCore (.val splitFn) (refExpr p)) s := by rfl

theorem merge_unfold (p q : Loc) (s : State) :
    Steps (mergeList p q) s (mergeCore (.val mergeFn) (refExpr p) (refExpr q)) s := by
  apply Steps.cons (show Step (mergeList p q) s
    (substBinder (some "args") (pair p q) (substBinder (some "mergeLists") mergeFn mergeBody)) s from rfl)
  apply steps_trans (steps_under (.letCtx (some "p") _) (struct_field _ (i := 0) (by rfl) s))
  apply Steps.cons (by rfl)
  apply steps_trans (steps_under (.letCtx (some "q") _) (struct_field _ (i := 1) (by rfl) s))
  exact .cons (by rfl) .refl

theorem sort_unfold (p : Loc) (s : State) :
    Step (sortList p) s (sortCore (.val sortFn) (refExpr p)) s := by rfl

/-- Split executes in CJR and returns two real list references. The input spine
and every other old object cell remain valid, including shared tails. -/
theorem split_correct (hp : Represents s p xs) (hb : Bounded s) :
    ∃ a b t, Evaluates (splitList p) s (pair a b) t ∧
      Represents t a (deal xs).1 ∧ Represents t b (deal xs).2 ∧ Preserves s t := by
  induction xs generalizing s p with
  | nil =>
    obtain ⟨hf⟩ := hp
    refine ⟨p,p,s,?_,.nil hf,.nil hf,Preserves.refl hb⟩
    apply Steps.cons (split_unfold _ _)
    apply Evaluates.if_false (field (value _ _) hf)
    exact struct_cons (value _ _) (struct_cons (value _ _) (struct_nil _ _))
  | cons x xs ih =>
    cases hp with
    | @cons _ _ q _ hf hv hn ht =>
      obtain ⟨a,b,t,he,ha,hb',hpres⟩ := ih ht hb
      let u := nodeState t true x (reference b)
      have hu : Preserves t u := Preserves.node hpres.bounded
      refine ⟨t.next,a,u,?_,cons_rep hb' hpres.bounded,represents_mono ha hu.extension,hpres.trans hu⟩
      apply Steps.cons (split_unfold _ _)
      apply Evaluates.if_true (field (value _ _) hf)
      apply Evaluates.letE (app_arg splitFn (field (value _ _) hn) he)
      apply struct_cons ?_
      · apply struct_cons (struct_field _ (i := 0) (by rfl) _)
        exact struct_nil _ _
      · apply new_cons (value _ _)
        apply new_cons (field (value _ _) (hpres.extension _ _ _ hv))
        exact new_cons (struct_field _ (i := 1) (by rfl) _) (new_nil _ _)

/-- Merge refines mathematical merge, including unsorted inputs. Sortedness is a
separate mathematical theorem, so the refinement does not assume its conclusion. -/
theorem merge_correct (hp : Represents s p xs) (hq : Represents s q ys) (hb : Bounded s) :
    ∃ r t, Evaluates (mergeList p q) s (reference r) t ∧
      Represents t r (merge xs ys) ∧ Preserves s t := by
  cases xs with
  | nil =>
    obtain ⟨hf⟩ := hp
    refine ⟨q,s,?_,by simpa only [merge] using hq,Preserves.refl hb⟩
    apply steps_trans (merge_unfold _ _ _)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | cons x xs =>
    cases hp with
    | @cons _ _ p' _ hf hv hn ht =>
      cases ys with
      | nil =>
        obtain ⟨hfalse⟩ := hq
        refine ⟨p,s,?_,by simpa only [merge] using Represents.cons hf hv hn ht,Preserves.refl hb⟩
        apply steps_trans (merge_unfold _ _ _)
        apply Evaluates.if_true (field (value _ _) hf)
        exact Evaluates.if_false (field (value _ _) hfalse) (value _ _)
      | cons y ys =>
        cases hq with
        | @cons _ _ q' _ hqf hqv hqn hqt =>
          have hpall := Represents.cons hf hv hn ht
          have hqall := Represents.cons hqf hqv hqn hqt
          by_cases hxy : x ≤ y
          · obtain ⟨r,t,he,hr,hpres⟩ := merge_correct ht hqall hb
            refine ⟨t.next,nodeState t true x (reference r),?_,?_,hpres.trans (Preserves.node hpres.bounded)⟩
            · apply steps_trans (merge_unfold _ _ _)
              apply Evaluates.if_true (field (value _ _) hf)
              apply Evaluates.if_true (field (value _ _) hqf)
              apply Evaluates.if_true (binop (field (value _ _) hv) (field (value _ _) hqv) ?_)
              · apply new_cons (value _ _)
                apply new_cons (field (value _ _) hv)
                apply new_cons (app_arg mergeFn ?_ he)
                · exact new_nil _ _
                · exact struct_cons (field (value _ _) hn) (struct_cons (value _ _) (struct_nil _ _))
              · simp [binOpEval,hxy]
            · simpa only [merge,hxy,↓reduceIte] using cons_rep hr hpres.bounded
          · obtain ⟨r,t,he,hr,hpres⟩ := merge_correct hpall hqt hb
            refine ⟨t.next,nodeState t true y (reference r),?_,?_,hpres.trans (Preserves.node hpres.bounded)⟩
            · apply steps_trans (merge_unfold _ _ _)
              apply Evaluates.if_true (field (value _ _) hf)
              apply Evaluates.if_true (field (value _ _) hqf)
              apply Evaluates.if_false (binop (field (value _ _) hv) (field (value _ _) hqv) ?_)
              · apply new_cons (value _ _)
                apply new_cons (field (value _ _) hqv)
                apply new_cons (app_arg mergeFn ?_ he)
                · exact new_nil _ _
                · exact struct_cons (value _ _) (struct_cons (field (value _ _) hqn) (struct_nil _ _))
              · simp [binOpEval,hxy]
            · simpa only [merge,hxy,↓reduceIte] using cons_rep hr hpres.bounded
termination_by xs.length + ys.length

end Cjr.LinkedList.MergeSort
