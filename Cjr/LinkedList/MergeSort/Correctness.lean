import Cjr.LinkedList.MergeSort.Helpers
namespace Cjr.LinkedList.MergeSort
open Evaluates

/-- Total correctness of the recursive CJR mergesort. Its output satisfies the
independent mathematical Sorting relation, and all pre-existing heap cells survive. -/
theorem sort_correct (hp : Represents s p xs) (hb : Bounded s) :
    ∃ output r t, Evaluates (sortList p) s (reference r) t ∧ Represents t r output ∧
      Sorting xs output ∧ Preserves s t := by
  cases xs with
  | nil =>
    obtain ⟨hf⟩ := hp
    refine ⟨[],p,s,?_,.nil hf,⟨.nil,.refl _⟩,Preserves.refl hb⟩
    apply Steps.cons (sort_unfold _ _)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)
  | cons x xs =>
    cases hp with
    | @cons _ _ q _ hf hv hn ht =>
      cases xs with
      | nil =>
        obtain ⟨hfalse⟩ := ht
        refine ⟨[x],p,s,?_,Represents.cons hf hv hn (.nil hfalse),⟨?_,.refl _⟩,Preserves.refl hb⟩
        · apply Steps.cons (sort_unfold _ _)
          apply Evaluates.if_true (field (value _ _) hf)
          apply Evaluates.letE (field (value _ _) hn)
          exact Evaluates.if_false (field (value _ _) hfalse) (value _ _)
        · exact .cons (by simp) .nil
      | cons y zs =>
        cases ht with
        | @cons _ _ q' _ hqf hqv hqn hqt =>
          have original := Represents.cons hf hv hn (Represents.cons hqf hqv hqn hqt)
          have small := deal_smaller (xs := x :: y :: zs) (by simp)
          obtain ⟨a,b,u,hsplit,ha,hb',hpres₀⟩ := split_correct original hb
          obtain ⟨sa,pa,v,hea,hpa,hsa,hpres₁⟩ := sort_correct ha hpres₀.bounded
          obtain ⟨sb,pb,w,heb,hpb,hsb,hpres₂⟩ :=
            sort_correct (represents_mono hb' hpres₁.extension) hpres₁.bounded
          obtain ⟨r,t,hem,hr,hpres₃⟩ :=
            merge_correct (represents_mono hpa hpres₂.extension) hpb hpres₂.bounded
          refine ⟨merge sa sb,r,t,?_,hr,?_,hpres₀.trans (hpres₁.trans (hpres₂.trans hpres₃))⟩
          · apply Steps.cons (sort_unfold _ _)
            apply Evaluates.if_true (field (value _ _) hf)
            apply Evaluates.letE (field (value _ _) hn)
            apply Evaluates.if_true (field (value _ _) hqf)
            apply Evaluates.letE hsplit
            apply Evaluates.letE (app_arg sortFn (struct_field _ (i := 0) (by rfl) _) hea)
            apply Evaluates.letE (app_arg sortFn (struct_field _ (i := 1) (by rfl) _) heb)
            apply app_arg mergeFn ?_ hem
            exact struct_cons (value _ _) (struct_cons (value _ _) (struct_nil _ _))
          · exact ⟨merge_ordered _ _ hsa.1 hsb.1,
              (merge_perm _ _).trans ((hsa.2.append hsb.2).trans (deal_perm _))⟩
termination_by xs.length

/-- Correctness for a CJR expression which computes the input list, rather than
only an already evaluated reference. -/
theorem sortExpr_correct (ha : Models s a xs) (hb : Bounded s) :
    ∃ output r t, Evaluates (sortExpr a) s (reference r) t ∧ Represents t r output ∧
      Sorting xs output ∧ Preserves s t := by
  obtain ⟨p,u,he,hp,hpres⟩ := ha s hb (extends_refl s)
  obtain ⟨output,r,t,hs,hr,hout,hpres'⟩ := sort_correct hp hpres.bounded
  exact ⟨output,r,t,app_arg sortFn he hs,hr,hout,hpres.trans hpres'⟩

/-- Every completed execution satisfies sortedness and permutation, by determinism. -/
theorem sort_all_results (hp : Represents s p xs) (hb : Bounded s)
    (he : Evaluates (sortList p) s (reference r) t) :
    ∃ output, Represents t r output ∧ Sorting xs output ∧ Preserves s t := by
  obtain ⟨output,r',t',he',hr,hout,hpres⟩ := sort_correct hp hb
  obtain ⟨hv,ht⟩ := evaluates_unique he' he
  have hrr : r' = r := by cases hv; rfl
  subst r'; subst t'
  exact ⟨output,hr,hout,hpres⟩

/-- No fixed fuel assumption: the operational derivation supplies a finite witness. -/
theorem sort_terminates (hp : Represents s p xs) (hb : Bounded s) :
    ∃ fuel output r t, run fuel (sortList p) s = .done (reference r) t ∧
      Represents t r output ∧ Sorting xs output ∧ Preserves s t := by
  obtain ⟨output,r,t,he,hr,hout,hpres⟩ := sort_correct hp hb
  obtain ⟨fuel,hf⟩ := evaluates_run he
  exact ⟨fuel,output,r,t,hf,hr,hout,hpres⟩

/-- A finite irreducible run cannot get stuck under the representation precondition. -/
theorem sort_no_stuck (hp : Represents s p xs) (hb : Bounded s)
    (he : Steps (sortList p) s e t) (hn : step e t = none) :
    ∃ output r, e = .val (reference r) ∧ Represents t r output ∧ Sorting xs output ∧ Preserves s t := by
  obtain ⟨output,r,u,he',hr,hout,hpres⟩ := sort_correct hp hb
  obtain ⟨heq,hs⟩ := steps_terminal_unique he' (value_stuck _ _) e t he hn
  subst e; subst u
  exact ⟨output,r,rfl,hr,hout,hpres⟩
end Cjr.LinkedList.MergeSort
