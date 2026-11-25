import Cjr.Syntax
namespace Cjr

/-- Finite maps implemented by association lists. Insert removes older bindings;
lookup and union have the same left-biased behavior as upstream gmap. -/
abbrev FMap (K V : Type) := List (K × V)
namespace FMap
 def lookup [DecidableEq K] (m : FMap K V) (k : K) : Option V :=
  match m with
  | [] => none
  | (a, v) :: rest => if k = a then some v else lookup rest k
 def erase [DecidableEq K] (m : FMap K V) (k : K) : FMap K V :=
  m.filter (fun p => decide (p.1 ≠ k))
 def insert [DecidableEq K] (m : FMap K V) (k : K) (v : V) : FMap K V :=
  (k, v) :: erase m k
 def union [DecidableEq K] (a b : FMap K V) : FMap K V :=
  a.foldr (fun (k,v) m => insert m k v) b
 @[simp] theorem lookup_insert [DecidableEq K] (m : FMap K V) (k : K) (v : V) :
     lookup (insert m k v) k = some v := by simp [insert, lookup]
end FMap

structure State where
  stack : FMap StackId Val := []
  raw : FMap RawId Val := []
  blocks : FMap RawId Nat := []
  obj : FMap (ObjId × Nat) Val := []
  next : Int := 0
  deriving Repr

def stateInit : State := {}
def setNth {α : Type} : Nat → α → List α → List α
  | _, _, [] => []
  | 0, a, _ :: xs => a :: xs
  | i+1, a, x :: xs => x :: setNth i a xs

def initCells (base : Loc) : Nat → FMap RawId Val
  | 0 => []
  | n+1 => (initCells base n).insert ⟨base + (n : Int)⟩ (.lit (.int 0))
def freeCells (base : Loc) : Nat → FMap RawId Val → FMap RawId Val
  | 0, m => m
  | n+1, m => (freeCells base n m).erase ⟨base + (n : Int)⟩
def initFields (o : Loc) : List Val → Nat → FMap (ObjId × Nat) Val
  | [], _ => []
  | v :: vs, i => (initFields o vs (i+1)).insert (⟨o⟩, i) v

/-- The six upstream well-formedness clauses, stated using lookup rather than domains. -/
structure StateWF (s : State) : Prop where
  stackBelow : ∀ l v, s.stack.lookup ⟨l⟩ = some v → l < s.next
  rawBelow : ∀ l v, s.raw.lookup ⟨l⟩ = some v → l < s.next
  blockBelow : ∀ l n, s.blocks.lookup ⟨l⟩ = some n → l < s.next
  objBelow : ∀ l i v, s.obj.lookup (⟨l⟩, i) = some v → l < s.next
  cover : ∀ l n, s.blocks.lookup ⟨l⟩ = some n →
    l + (n : Int) ≤ s.next ∧ ∀ i, i < n → ∃ v, s.raw.lookup ⟨l + (i : Int)⟩ = some v
  disjoint : ∀ l₁ n₁ l₂ n₂, s.blocks.lookup ⟨l₁⟩ = some n₁ →
    s.blocks.lookup ⟨l₂⟩ = some n₂ → l₁ ≠ l₂ →
    l₁ + (n₁ : Int) ≤ l₂ ∨ l₂ + (n₂ : Int) ≤ l₁

theorem stateInit_wf : StateWF stateInit := by
  constructor <;> simp [stateInit, FMap.lookup]
theorem stack_fresh (h : StateWF s) : s.stack.lookup ⟨s.next⟩ = none := by
  cases he : s.stack.lookup ⟨s.next⟩ with
  | none => rfl
  | some v => exact False.elim (Int.lt_irrefl s.next (h.stackBelow s.next v he))
theorem raw_fresh (h : StateWF s) : s.raw.lookup ⟨s.next⟩ = none := by
  cases he : s.raw.lookup ⟨s.next⟩ with
  | none => rfl
  | some v => exact False.elim (Int.lt_irrefl s.next (h.rawBelow s.next v he))
theorem block_fresh (h : StateWF s) : s.blocks.lookup ⟨s.next⟩ = none := by
  cases he : s.blocks.lookup ⟨s.next⟩ with
  | none => rfl
  | some v => exact False.elim (Int.lt_irrefl s.next (h.blockBelow s.next v he))
theorem obj_fresh (h : StateWF s) (i : Nat) : s.obj.lookup (⟨s.next⟩, i) = none := by
  cases he : s.obj.lookup (⟨s.next⟩, i) with
  | none => rfl
  | some v => exact False.elim (Int.lt_irrefl s.next (h.objBelow s.next i v he))
end Cjr
