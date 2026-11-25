import Std

namespace Cjr.LinkedList.MergeSort

/-- Algorithm-independent specification: every earlier element is at most every
later element, and the output is a permutation (with multiplicities) of input. -/
def Ordered (xs : List Int) : Prop := xs.Pairwise (· ≤ ·)
def Sorting (input output : List Int) : Prop := Ordered output ∧ output.Perm input

/-- Alternating balanced split, used only to describe the CJR split's result. -/
def deal : List Int → List Int × List Int
  | [] => ([],[])
  | x :: xs => let (a,b) := deal xs; (x :: b,a)

theorem deal_lengths (xs : List Int) :
    (deal xs).1.length + (deal xs).2.length = xs.length ∧
    (deal xs).2.length ≤ (deal xs).1.length ∧
    (deal xs).1.length ≤ (deal xs).2.length + 1 := by
  induction xs with
  | nil => simp [deal]
  | cons x xs ih =>
    rcases hd : deal xs with ⟨a,b⟩
    simp only [hd] at ih
    simp only [deal,hd,List.length_cons]
    constructor
    · omega
    · constructor <;> omega

theorem deal_smaller (h : 2 ≤ xs.length) :
    (deal xs).1.length < xs.length ∧ (deal xs).2.length < xs.length := by
  obtain ⟨ht,hl,hr⟩ := deal_lengths xs
  constructor <;> omega

theorem deal_perm (xs : List Int) : ((deal xs).1 ++ (deal xs).2).Perm xs := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    rcases hd : deal xs with ⟨a,b⟩
    simp only [hd] at ih
    change ((x :: (deal xs).2) ++ (deal xs).1).Perm (x :: xs)
    rw [hd]
    exact .cons x (List.perm_append_comm.trans ih)

/-- Mathematical merge, separate from both heap representation and execution. -/
def merge : List Int → List Int → List Int
  | [],ys => ys
  | xs,[] => xs
  | x :: xs,y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

theorem merge_perm (xs ys : List Int) : (merge xs ys).Perm (xs ++ ys) := by
  fun_induction merge xs ys
  · exact .refl _
  · simp
  · exact .cons _ (by assumption)
  · exact (List.Perm.cons _ (by assumption)).trans List.perm_middle.symm

theorem merge_lower (hx : ∀ v ∈ xs, z ≤ v) (hy : ∀ v ∈ ys, z ≤ v) :
    ∀ v ∈ merge xs ys, z ≤ v := by
  intro v hv
  rcases List.mem_append.mp ((merge_perm xs ys).mem_iff.mp hv) with h | h
  · exact hx v h
  · exact hy v h

theorem merge_ordered (xs ys : List Int) : Ordered xs → Ordered ys → Ordered (merge xs ys) := by
  fun_induction merge xs ys
  · intro _ h; exact h
  · intro h _; exact h
  · intro hx hy
    apply List.Pairwise.cons
    · apply merge_lower (fun v hv => List.rel_of_pairwise_cons hx hv)
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · subst v; assumption
      · exact Int.le_trans (by assumption) (List.rel_of_pairwise_cons hy h)
    · apply_assumption
      · exact hx.of_cons
      · exact hy
  · intro hx hy
    apply List.Pairwise.cons
    · apply merge_lower
      · intro v hv
        rcases List.mem_cons.mp hv with h | h
        · subst v; omega
        · exact Int.le_trans (by omega) (List.rel_of_pairwise_cons hx h)
      · exact fun v hv => List.rel_of_pairwise_cons hy hv
    · apply_assumption
      · exact hx
      · exact hy.of_cons

/-- Permutation includes duplicates, not just membership or equal length. -/
theorem Sorting.count_eq (h : Sorting input output) (x : Int) : output.count x = input.count x :=
  h.2.count_eq x
end Cjr.LinkedList.MergeSort
