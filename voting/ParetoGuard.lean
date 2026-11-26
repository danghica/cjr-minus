import ReturnSafety
import Canonical

namespace Cjr.Voting

/-- Strict preference on a possibly partial ranking: A is present, and precedes
B. An omitted B has index `row.length`, below every ranked candidate. -/
def Prefers (row : List Nat) (a b : Nat) : Prop :=
  a ∈ row ∧ row.idxOf a < row.idxOf b

/-- Unanimity is a claim about a nonempty electorate. -/
def UnanimouslyPrefers (bs : List (List Nat)) (a b : Nat) : Prop :=
  bs ≠ [] ∧ ∀ row ∈ bs, Prefers row a b

def unanimousAbove (bs : List (List Nat)) (a b : Nat) : Bool :=
  !bs.isEmpty && bs.all (fun row => row.contains a && decide (row.idxOf a < row.idxOf b))

theorem unanimousAbove_iff : unanimousAbove bs a b = true ↔ UnanimouslyPrefers bs a b := by
  simp [unanimousAbove,UnanimouslyPrefers,Prefers]

/-- All candidates not unanimously dominated by another valid candidate. Empty
electorates have no admissible winner. Multiplicity and voter order are irrelevant. -/
def paretoCandidates (n : Nat) (bs : List (List Nat)) : List Nat :=
  if bs.isEmpty then [] else
    (List.range n).filter (fun b => !(List.range n).any (fun a => unanimousAbove bs a b))

theorem paretoCandidates_excludes (ha : a < n) (hu : UnanimouslyPrefers bs a b) :
    b ∉ paretoCandidates n bs := by
  intro hm
  have hun := unanimousAbove_iff.mpr hu
  have hany : (List.range n).any (fun c => unanimousAbove bs c b) = true :=
    List.any_eq_true.mpr ⟨a,List.mem_range.mpr ha,hun⟩
  simp [paretoCandidates] at hm
  simp_all

theorem unanimouslyPrefers_perm (h : bs.Perm cs) :
    UnanimouslyPrefers bs a b ↔ UnanimouslyPrefers cs a b := by
  have hempty : bs = [] ↔ cs = [] := by
    constructor <;> intro hempty
    · simpa [hempty] using h.length_eq.symm
    · simpa [hempty] using h.length_eq
  constructor
  · rintro ⟨hne,hall⟩
    exact ⟨fun hc => hne (hempty.mpr hc),fun row hr => hall row (h.mem_iff.mpr hr)⟩
  · rintro ⟨hne,hall⟩
    exact ⟨fun hb => hne (hempty.mp hb),fun row hr => hall row (h.mem_iff.mp hr)⟩

/-- The CJR guard returns an explicitly allowed integer, or -1. It never returns
the unchecked expression directly. Conditions may contain arbitrary expressions. -/
def allowedResult (allowed : List Nat) (answer : Expr) : Expr :=
  match allowed with
  | [] => .val (.lit (.int (-1)))
  | c :: cs => .ifE (.binOp .eq answer (.val (.lit (.int c))))
      (.val (.lit (.int c))) (allowedResult cs answer)

def AllowedValue (allowed : List Nat) (v : Val) : Prop :=
  v = .lit (.int (-1)) ∨ ∃ c ∈ allowed, v = .lit (.int c)

theorem allowedValue_nat_member {b : Nat} {allowed : List Nat} (h : AllowedValue allowed (.lit (.int b))) : b ∈ allowed := by
  rcases h with hneg | ⟨c,hc,hval⟩
  · have hbad : (b : Int) = -1 := by
      simpa only [Val.lit.injEq,Lit.int.injEq] using hneg
    omega
  · have hbc : b = c := by
      simpa only [Val.lit.injEq,Lit.int.injEq,Int.ofNat_inj] using hval
    exact hbc ▸ hc

theorem allowedResult_safe (allowed : List Nat) (answer : Expr) :
    ReturnsOnly (AllowedValue allowed) (allowedResult allowed answer) := by
  induction allowed with
  | nil => exact .value (.inl rfl)
  | cons c cs ih =>
    apply ReturnsOnly.ifE
    · exact .value (.inr ⟨c,List.mem_cons_self,rfl⟩)
    · -- The tail's result certificate is proved directly with the larger allowed set.
      clear ih
      have aux : ∀ xs : List Nat, (∀ x ∈ xs, x ∈ c :: cs) →
          ReturnsOnly (AllowedValue (c :: cs)) (allowedResult xs answer) := by
        intro xs
        induction xs with
        | nil => intro _; exact .value (.inl rfl)
        | cons x xs ih =>
          intro hm
          exact .ifE (.value (.inr ⟨x,hm x List.mem_cons_self,rfl⟩))
            (ih (fun y hy => hm y (List.mem_cons_of_mem x hy)))
      exact aux cs (fun x hx => List.mem_cons_of_mem c hx)

theorem allowedResult_subst (allowed : List Nat) (answer : Expr) (x : String) (v : Val) :
    subst x v (allowedResult allowed answer) = allowedResult allowed (subst x v answer) := by
  induction allowed with
  | nil => rfl
  | cons c cs ih =>
    simp only [allowedResult,subst,substitute,substituteVal] at ih ⊢
    rw [ih]

/-- Runs the existing CJR election and checks its returned candidate in CJR.
A failed check returns the existing no-winner/error sentinel -1. -/
def paretoGuard (n : Nat) (bs : List (List Nat)) (core : Expr) : Expr :=
  .letE (some "paretoWinner") core
    (allowedResult (paretoCandidates n bs) (.var "paretoWinner"))

theorem paretoGuard_safe (n : Nat) (bs : List (List Nat)) (core : Expr) :
    ReturnsOnly (AllowedValue (paretoCandidates n bs)) (paretoGuard n bs core) := by
  apply ReturnsOnly.letE
  intro v
  change ReturnsOnly _ (subst "paretoWinner" v _)
  rw [allowedResult_subst]
  exact allowedResult_safe _ _

/-- An eligible result is actually accepted, with no further state changes. -/
theorem allowedResult_accepts {c : Nat} {allowed : List Nat} (hc : c ∈ allowed) (s : State) :
    Evaluates (allowedResult allowed (.val (.lit (.int c)))) s (.lit (.int c)) s := by
  induction allowed with
  | nil => simp at hc
  | cons a rest ih =>
    by_cases heq : c = a
    · subst a
      apply Evaluates.if_true
      · exact Evaluates.binop (.value _ _) (.value _ _) (by simp [binOpEval])
      · exact .value _ _
    · apply Evaluates.if_false
      · exact Evaluates.binop (.value _ _) (.value _ _) (by simp [binOpEval,Int.ofNat_inj,heq])
      · exact ih ((List.mem_cons.mp hc).resolve_left heq)

theorem paretoGuard_accepts {c : Nat} (hc : c ∈ paretoCandidates n bs)
    (hrun : Evaluates core s (.lit (.int c)) t) :
    Evaluates (paretoGuard n bs core) s (.lit (.int c)) t := by
  apply Evaluates.letE hrun
  change Evaluates (subst "paretoWinner" (.lit (.int c)) _) t _ t
  rw [allowedResult_subst]
  exact allowedResult_accepts hc t

end Cjr.Voting
