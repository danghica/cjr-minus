import Cjr.CountedExecution
import Cjr.LinkedList.MergeSort.Correctness
import Cjr.LinkedList.MergeSort.CostModel
namespace Cjr.LinkedList.MergeSort
open Exec

theorem merge_unfold_counted (p q : Loc) (s : State) :
    StepsN 5 (mergeList p q) s (mergeCore (.val mergeFn) (refExpr p) (refExpr q)) s := by
  apply StepsN.cons (show Step (mergeList p q) s
    (substBinder (some "args") (pair p q) (substBinder (some "mergeLists") mergeFn mergeBody)) s from rfl)
  apply StepsN.trans (m := 3) (StepsN.under (.letCtx (some "p") _) (struct_field _ (i := 0) (by rfl) s))
  apply StepsN.cons (by rfl)
  apply StepsN.trans (m := 1) (StepsN.under (.letCtx (some "q") _) (struct_field _ (i := 1) (by rfl) s))
  exact .cons (by rfl) .refl

theorem split_counted (hp : Represents s p xs) (hb : Bounded s) :
    ∃ a b t, Exec (splitSteps xs.length) (splitList p) s (pair a b) t ∧
      Represents t a (deal xs).1 ∧ Represents t b (deal xs).2 ∧ Preserves s t := by
  induction xs generalizing s p with
  | nil =>
    obtain ⟨hf⟩ := hp
    have he : Exec 6 (splitList p) s (pair p p) s := by
      apply Exec.recost
      · apply StepsN.cons (split_unfold _ _)
        apply Exec.if_false (field (value _ _) hf)
        exact struct_cons (value _ _) (struct_cons (value _ _) (struct_nil _ _))
      · rfl
    exact ⟨p,p,s,he,.nil hf,.nil hf,Preserves.refl hb⟩
  | cons x xs ih =>
    cases hp with
    | @cons _ _ q _ hf hv hn ht =>
      obtain ⟨a,b,t,he,ha,hb',hpres⟩ := ih ht hb
      let u := nodeState t true x (reference b)
      have hu : Preserves t u := Preserves.node hpres.bounded
      have hex : Exec (splitSteps (x :: xs).length) (splitList p) s (pair t.next a) u := by
        apply Exec.recost
        · apply StepsN.cons (split_unfold _ _)
          apply Exec.if_true (field (value _ _) hf)
          apply Exec.letE (app_arg splitFn (field (value _ _) hn) he)
          apply struct_cons (n := 6) ?_
          · apply struct_cons (struct_field _ (i := 0) (by rfl) _)
            exact struct_nil _ _
          · exact new_cons (value _ _) (new_cons (field (value _ _) (hpres.extension _ _ _ hv))
              (new_cons (struct_field _ (i := 1) (by rfl) _) (new_nil _ _)))
        · simp only [splitSteps,List.length_cons,Nat.mul_succ]; omega
      refine ⟨t.next,a,u,?_,cons_rep hb' hpres.bounded,represents_mono ha hu.extension,hpres.trans hu⟩
      exact hex

theorem merge_counted (hp : Represents s p xs) (hq : Represents s q ys) (hb : Bounded s) :
    ∃ r t, Exec (mergeSteps xs ys) (mergeList p q) s (reference r) t ∧
      Represents t r (merge xs ys) ∧ Preserves s t := by
  cases xs with
  | nil =>
    obtain ⟨hf⟩ := hp
    have he : Exec 7 (mergeList p q) s (reference q) s := by
      apply Exec.recost
      · apply StepsN.trans (merge_unfold_counted _ _ _)
        exact Exec.if_false (field (value _ _) hf) (value _ _)
      · rfl
    refine ⟨q,s,?_,by simpa only [merge] using hq,Preserves.refl hb⟩
    simpa only [mergeSteps] using he
  | cons x xs =>
    cases hp with
    | @cons _ _ p' _ hf hv hn ht =>
      cases ys with
      | nil =>
        obtain ⟨hfalse⟩ := hq
        have he : Exec 9 (mergeList p q) s (reference p) s := by
          apply Exec.recost
          · apply StepsN.trans (merge_unfold_counted _ _ _)
            apply Exec.if_true (field (value _ _) hf)
            exact Exec.if_false (field (value _ _) hfalse) (value _ _)
          · rfl
        refine ⟨p,s,?_,by simpa only [merge] using Represents.cons hf hv hn ht,Preserves.refl hb⟩
        simpa only [mergeSteps] using he
      | cons y ys =>
        cases hq with
        | @cons _ _ q' _ hqf hqv hqn hqt =>
          have hpall := Represents.cons hf hv hn ht
          have hqall := Represents.cons hqf hqv hqn hqt
          by_cases hxy : x ≤ y
          · obtain ⟨r,t,he,hr,hpres⟩ := merge_counted ht hqall hb
            have hex : Exec (mergeSteps (x :: xs) (y :: ys)) (mergeList p q) s (reference t.next) (nodeState t true x (reference r)) := by
              apply Exec.recost
              · apply StepsN.trans (merge_unfold_counted _ _ _)
                apply Exec.if_true (field (value _ _) hf)
                apply Exec.if_true (field (value _ _) hqf)
                apply Exec.if_true (binop (field (value _ _) hv) (field (value _ _) hqv) ?_)
                · apply new_cons (value _ _)
                  apply new_cons (field (value _ _) hv)
                  apply new_cons (app_arg mergeFn (n := 4) ?_ he)
                  · exact new_nil _ _
                  · exact struct_cons (field (value _ _) hn) (struct_cons (value _ _) (struct_nil _ _))
                · simp [binOpEval,hxy]
              · simp only [mergeSteps,hxy,↓reduceIte]; omega
            refine ⟨t.next,nodeState t true x (reference r),?_,?_,hpres.trans (Preserves.node hpres.bounded)⟩
            · exact hex
            · simpa only [merge,hxy,↓reduceIte] using cons_rep hr hpres.bounded
          · obtain ⟨r,t,he,hr,hpres⟩ := merge_counted hpall hqt hb
            have hex : Exec (mergeSteps (x :: xs) (y :: ys)) (mergeList p q) s (reference t.next) (nodeState t true y (reference r)) := by
              apply Exec.recost
              · apply StepsN.trans (merge_unfold_counted _ _ _)
                apply Exec.if_true (field (value _ _) hf)
                apply Exec.if_true (field (value _ _) hqf)
                apply Exec.if_false (binop (field (value _ _) hv) (field (value _ _) hqv) ?_)
                · apply new_cons (value _ _)
                  apply new_cons (field (value _ _) hqv)
                  apply new_cons (app_arg mergeFn (n := 4) ?_ he)
                  · exact new_nil _ _
                  · exact struct_cons (value _ _) (struct_cons (field (value _ _) hqn) (struct_nil _ _))
                · simp [binOpEval,hxy]
              · simp only [mergeSteps,hxy,↓reduceIte]; omega
            refine ⟨t.next,nodeState t true y (reference r),?_,?_,hpres.trans (Preserves.node hpres.bounded)⟩
            · exact hex
            · simpa only [merge,hxy,↓reduceIte] using cons_rep hr hpres.bounded
termination_by xs.length + ys.length

/-- Exact transition count, proved from Step rather than an assumed recurrence. -/
theorem sort_counted (hp : Represents s p xs) (hb : Bounded s) :
    ∃ r t, Exec (sortSteps xs) (sortList p) s (reference r) t ∧
      Represents t r (sorted xs) ∧ Preserves s t := by
  cases xs with
  | nil =>
    obtain ⟨hf⟩ := hp
    have he : Exec 3 (sortList p) s (reference p) s := by
      apply Exec.recost
      · apply StepsN.cons (sort_unfold _ _)
        exact Exec.if_false (field (value _ _) hf) (value _ _)
      · rfl
    refine ⟨p,s,?_,?_,Preserves.refl hb⟩
    · simpa only [sortSteps] using he
    · simpa only [sorted] using Represents.nil hf
  | cons x xs =>
    cases hp with
    | @cons _ _ q _ hf hv hn ht =>
      cases xs with
      | nil =>
        obtain ⟨hfalse⟩ := ht
        have he : Exec 7 (sortList p) s (reference p) s := by
          apply Exec.recost
          · apply StepsN.cons (sort_unfold _ _)
            apply Exec.if_true (field (value _ _) hf)
            apply Exec.letE (field (value _ _) hn)
            exact Exec.if_false (field (value _ _) hfalse) (value _ _)
          · rfl
        refine ⟨p,s,?_,?_,Preserves.refl hb⟩
        · simpa only [sortSteps] using he
        · simpa only [sorted] using Represents.cons hf hv hn (Represents.nil hfalse)
      | cons y zs =>
        cases ht with
        | @cons _ _ q' _ hqf hqv hqn hqt =>
          have original := Represents.cons hf hv hn (Represents.cons hqf hqv hqn hqt)
          have small := deal_smaller (xs := x :: y :: zs) (by simp)
          obtain ⟨a,b,u,hsplit,ha,hb',hpres₀⟩ := split_counted original hb
          obtain ⟨pa,v,hea,hpa,hpres₁⟩ := sort_counted ha hpres₀.bounded
          obtain ⟨pb,w,heb,hpb,hpres₂⟩ :=
            sort_counted (represents_mono hb' hpres₁.extension) hpres₁.bounded
          obtain ⟨r,t,hem,hr,hpres₃⟩ :=
            merge_counted (represents_mono hpa hpres₂.extension) hpb hpres₂.bounded
          have hex : Exec (sortSteps (x :: y :: zs)) (sortList p) s (reference r) t := by
            apply Exec.recost
            · apply StepsN.cons (sort_unfold _ _)
              apply Exec.if_true (field (value _ _) hf)
              apply Exec.letE (field (value _ _) hn)
              apply Exec.if_true (field (value _ _) hqf)
              apply Exec.letE hsplit
              apply Exec.letE (app_arg sortFn (struct_field _ (i := 0) (by rfl) _) hea)
              apply Exec.letE (app_arg sortFn (struct_field _ (i := 1) (by rfl) _) heb)
              apply app_arg mergeFn (n := 3) ?_ hem
              exact struct_cons (value _ _) (struct_cons (value _ _) (struct_nil _ _))
            · simp only [sortSteps]; omega
          refine ⟨r,t,?_,?_,hpres₀.trans (hpres₁.trans (hpres₂.trans hpres₃))⟩
          · exact hex
          · simpa only [sorted] using hr
termination_by xs.length

end Cjr.LinkedList.MergeSort
