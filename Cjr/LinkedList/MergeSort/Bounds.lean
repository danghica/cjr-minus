import Cjr.LinkedList.MergeSort.Counted
namespace Cjr.LinkedList.MergeSort

private theorem halves_upper (hn : 2 ≤ xs.length) (hp : xs.length ≤ 2^(k+1)) :
    0 < (deal xs).1.length ∧ 0 < (deal xs).2.length ∧
    (deal xs).1.length ≤ 2^k ∧ (deal xs).2.length ≤ 2^k := by
  obtain ⟨ht,hl,hr⟩ := deal_lengths xs
  rw [Nat.two_pow_succ] at hp
  have hpos := Nat.one_le_two_pow (n := k)
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private theorem halves_lower (hp : 2^(k+1) ≤ xs.length) :
    2^k ≤ (deal xs).1.length ∧ 2^k ≤ (deal xs).2.length := by
  obtain ⟨ht,hl,hr⟩ := deal_lengths xs
  rw [Nat.two_pow_succ] at hp
  constructor <;> omega

/-- Height-k tree bound. The +30 pays the administrative cost uniformly,
including merge's two different empty-input branches. -/
theorem upper_height (k : Nat) : ∀ xs : List Int, 0 < xs.length → xs.length ≤ 2^k →
    sortSteps xs + 30 ≤ 37*xs.length*(k+1) := by
  induction k with
  | zero =>
    intro xs hn hp
    cases xs with
    | nil => simp at hn
    | cons x xs => cases xs with
      | nil => simp [sortSteps]
      | cons y ys => simp at hp
  | succ k ih =>
    intro xs hn hp
    cases xs with
    | nil => simp at hn
    | cons x xs => cases xs with
      | nil => simp only [sortSteps,List.length_cons,List.length_nil]; omega
      | cons y ys =>
        let input := x :: y :: ys
        let a := (deal input).1
        let b := (deal input).2
        obtain ⟨ha,hb,hpa,hpb⟩ := halves_upper (xs := input) (by simp [input]) hp
        have hca := ih a ha hpa
        have hcb := ih b hb hpb
        have hm := mergeSteps_bound (sorted a) (sorted b)
        simp only [sorted_length] at hm
        have ht : a.length+b.length=input.length := (deal_lengths input).1
        have hsum : 37*a.length*(k+1)+37*b.length*(k+1)=37*input.length*(k+1) := by
          rw [← Nat.add_mul,← Nat.mul_add,ht]
        rw [ht] at hm
        change sortSteps input+30 ≤ 37*input.length*((k+1)+1)
        rw [Nat.mul_succ]
        rw [sortSteps]
        change splitSteps input.length+15+sortSteps a+sortSteps b+mergeSteps (sorted a) (sorted b)+30 ≤ _
        simp only [splitSteps]
        omega

/-- Splitting alone forces logarithmic work even on already sorted input. -/
theorem lower_height (k : Nat) : ∀ xs : List Int, 2^k ≤ xs.length →
    15*xs.length*k ≤ sortSteps xs := by
  induction k with
  | zero => intro xs _; simp
  | succ k ih =>
    intro xs hp
    have hpos := Nat.one_le_two_pow (n := k)
    have htwo : 2 ≤ xs.length := by rw [Nat.two_pow_succ] at hp; omega
    cases xs with
    | nil => simp at htwo
    | cons x xs => cases xs with
      | nil => simp at htwo
      | cons y ys =>
        let input := x :: y :: ys
        let a := (deal input).1
        let b := (deal input).2
        obtain ⟨hpa,hpb⟩ := halves_lower (xs := input) hp
        have hca := ih a hpa
        have hcb := ih b hpb
        have ht : a.length+b.length=input.length := (deal_lengths input).1
        have hsum : 15*a.length*k+15*b.length*k=15*input.length*k := by
          rw [← Nat.add_mul,← Nat.mul_add,ht]
        change 15*input.length*(k+1) ≤ sortSteps input
        rw [Nat.mul_succ]
        rw [sortSteps]
        change 15*input.length*k+15*input.length ≤
          splitSteps input.length+15+sortSteps a+sortSteps b+mergeSteps (sorted a) (sorted b)
        simp only [splitSteps]
        omega

/-- A safe size-only worst-case budget, in CJR transitions, excluding construction
of the input list. It is an upper envelope, not a claim of exact worst-case attainment. -/
def worstBudget (n : Nat) : Nat := if n=0 then 3 else 37*n*(ceilLog n+1)-30

theorem sortSteps_bounds (xs : List Int) :
    15*xs.length*xs.length.log2 ≤ sortSteps xs ∧ sortSteps xs ≤ worstBudget xs.length := by
  by_cases hn : xs.length=0
  · have hx : xs=[] := List.eq_nil_of_length_eq_zero hn
    subst xs
    simp [sortSteps,worstBudget]
  · have hp : 0 < xs.length := by omega
    have hl := lower_height xs.length.log2 xs (Nat.log2_self_le hn)
    have hu := upper_height (ceilLog xs.length) xs hp (ceilLog_power _)
    refine ⟨hl,?_⟩
    simp only [worstBudget,hn,↓reduceIte]
    omega

/-- General formal complexity theorem about the executable CJR implementation. -/
theorem operational_bound (hp : Represents s p xs) (hb : Bounded s) :
    ∃ r t, Exec (sortSteps xs) (sortList p) s (reference r) t ∧
      Represents t r (sorted xs) ∧ Preserves s t ∧
      15*xs.length*xs.length.log2 ≤ sortSteps xs ∧ sortSteps xs ≤ worstBudget xs.length := by
  obtain ⟨r,t,he,hr,hpres⟩ := sort_counted hp hb
  exact ⟨r,t,he,hr,hpres,sortSteps_bounds xs⟩

/-- Every terminating trace has the modeled count, not just one chosen derivation. -/
theorem every_execution_bound (hp : Represents s p xs) (hb : Bounded s)
    (he : Exec steps (sortList p) s v t) :
    steps=sortSteps xs ∧ 15*xs.length*xs.length.log2 ≤ steps ∧ steps ≤ worstBudget xs.length := by
  obtain ⟨r,u,hcanon,_,_⟩ := sort_counted hp hb
  have hc := (exec_unique hcanon he).1
  exact ⟨hc.symm,by simpa only [hc] using sortSteps_bounds xs⟩

/-- An explicit constant-factor Theta(n floor(log2 n)) statement for n >= 2.
Both sides apply to every input, hence also bound the worst case. -/
theorem theta_n_log2 (hn : 2 ≤ xs.length) :
    15*xs.length*xs.length.log2 ≤ sortSteps xs ∧ sortSteps xs ≤ 111*xs.length*xs.length.log2 := by
  obtain ⟨hl,hu⟩ := sortSteps_bounds xs
  have hne : xs.length ≠ 0 := by omega
  have hk : 1 ≤ xs.length.log2 := (Nat.le_log2 hne).mpr (by simpa using hn)
  have hc : ceilLog xs.length ≤ xs.length.log2+1 :=
    (ceilLog_le_iff (n := xs.length)).mpr (Nat.le_of_lt Nat.lt_log2_self)
  have hfac : ceilLog xs.length+1 ≤ 3*xs.length.log2 := by omega
  have hm := Nat.mul_le_mul_left (37*xs.length) hfac
  have heq : 37*xs.length*(3*xs.length.log2)=111*xs.length*xs.length.log2 := by
    calc
      _ = 37*(3*(xs.length*xs.length.log2)) := by
        rw [Nat.mul_assoc,Nat.mul_left_comm xs.length 3 _]
      _ = _ := by simp [← Nat.mul_assoc]
  rw [heq] at hm
  simp only [worstBudget,hne,↓reduceIte] at hu
  exact ⟨hl,Nat.le_trans hu (Nat.le_trans (Nat.sub_le _ _) hm)⟩

/-- The size-only worst-case budget is enough fuel for the actual interpreter. -/
theorem budget_suffices (hp : Represents s p xs) (hb : Bounded s) :
    ∃ r t, run (worstBudget xs.length) (sortList p) s = .done (reference r) t ∧
      Represents t r (sorted xs) ∧ Preserves s t := by
  obtain ⟨r,t,he,hr,hpres⟩ := sort_counted hp hb
  have hf := Exec.run he (worstBudget xs.length-sortSteps xs)
  have hn := (sortSteps_bounds xs).2
  rw [Nat.add_sub_of_le hn] at hf
  exact ⟨r,t,hf,hr,hpres⟩

/-- Direct constant-factor complexity statement for an arbitrary actual execution. -/
theorem execution_theta (hp : Represents s p xs) (hb : Bounded s)
    (he : Exec steps (sortList p) s v t) (hn : 2 ≤ xs.length) :
    15*xs.length*xs.length.log2 ≤ steps ∧ steps ≤ 111*xs.length*xs.length.log2 := by
  have hc := (every_execution_bound hp hb he).1
  simpa only [hc] using theta_n_log2 hn

end Cjr.LinkedList.MergeSort
