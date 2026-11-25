import Cjr.LinkedList.MergeSort.Math

namespace Cjr.LinkedList.MergeSort

/-- Pure reference mergesort, used to express the exact value-dependent cost.
It is not substituted for the CJR implementation. -/
def sorted : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    merge (sorted (deal (x :: y :: xs)).1) (sorted (deal (x :: y :: xs)).2)
termination_by xs => xs.length
decreasing_by
  · exact (deal_smaller (by simp)).1
  · exact (deal_smaller (by simp)).2

theorem sorted_spec (xs : List Int) : Sorting xs (sorted xs) := by
  cases xs with
  | nil => rw [sorted]; exact ⟨.nil,.refl _⟩
  | cons x xs => cases xs with
    | nil => rw [sorted]; exact ⟨.cons (by simp) .nil,.refl _⟩
    | cons y ys =>
      have ha := sorted_spec (deal (x :: y :: ys)).1
      have hb := sorted_spec (deal (x :: y :: ys)).2
      rw [sorted]
      exact ⟨merge_ordered _ _ ha.1 hb.1,
        (merge_perm _ _).trans ((ha.2.append hb.2).trans (deal_perm _))⟩
termination_by xs.length
decreasing_by
  · exact (deal_smaller (by simp)).1
  · exact (deal_smaller (by simp)).2

theorem sorted_length (xs : List Int) : (sorted xs).length = xs.length := (sorted_spec xs).2.length_eq

def splitSteps (n : Nat) : Nat := 15*n+6

def mergeSteps : List Int → List Int → Nat
  | [],_ => 7
  | _ :: _,[] => 9
  | x :: xs,y :: ys =>
    22 + if x ≤ y then mergeSteps xs (y :: ys) else mergeSteps (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Exact cost of a call on an already represented list; construction of the
input list is excluded. The cost bridge proves every constant against Step. -/
def sortSteps : List Int → Nat
  | [] => 3
  | [_] => 7
  | x :: y :: xs =>
    let a := (deal (x :: y :: xs)).1
    let b := (deal (x :: y :: xs)).2
    splitSteps (x :: y :: xs).length + 15 + sortSteps a + sortSteps b + mergeSteps (sorted a) (sorted b)
termination_by xs => xs.length
decreasing_by
  · exact (deal_smaller (by simp)).1
  · exact (deal_smaller (by simp)).2

-- splitSteps includes its own +6, so splitSteps(n)+15 is 15*n+21.
theorem mergeSteps_bound (xs ys : List Int) : mergeSteps xs ys ≤ 22*(xs.length+ys.length)+9 := by
  fun_induction mergeSteps xs ys <;> simp_all only [List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_succ]
  all_goals try split
  all_goals omega

/-- The ceiling binary logarithm, with ceilLog 0 = ceilLog 1 = 0. -/
def ceilLog (n : Nat) : Nat := if n ≤ 1 then 0 else (n-1).log2+1

theorem ceilLog_le_iff : ceilLog n ≤ k ↔ n ≤ 2^k := by
  by_cases h : n ≤ 1
  · have hp := Nat.one_le_two_pow (n := k)
    simp only [ceilLog,h,↓reduceIte]
    exact ⟨fun _ => Nat.le_trans h hp,fun _ => Nat.zero_le _⟩
  · have hn' : n-1 ≠ 0 := by omega
    have hl := Nat.log2_lt (n := n-1) (k := k) hn'
    simp only [ceilLog,h,↓reduceIte]
    constructor
    · intro hc
      have hlt : (n-1).log2 < k := by omega
      have hh := hl.mp hlt
      omega
    · intro hp
      have hh : n-1 < 2^k := by omega
      have hlt := hl.mpr hh
      omega

theorem ceilLog_power (n : Nat) : n ≤ 2^(ceilLog n) :=
  ceilLog_le_iff.mp (Nat.le_refl _)
end Cjr.LinkedList.MergeSort
