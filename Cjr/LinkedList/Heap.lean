import Cjr.LinkedList.Code

namespace Cjr.FMap
 theorem lookup_erase_ne [DecidableEq K] (m : FMap K V) (k q : K) (h : q ≠ k) :
    lookup (erase m k) q = lookup m q := by
  induction m with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,v⟩
    by_cases ha : a = k
    · subst a
      simpa [erase, lookup, h] using ih
    · by_cases hqa : q = a
      · simp [erase, lookup, ha, hqa]
      · simpa [erase, lookup, ha, hqa] using ih
 theorem lookup_insert_ne [DecidableEq K] (m : FMap K V) (k q : K) (v : V) (h : q ≠ k) :
    lookup (insert m k v) q = lookup m q := by
  simp only [insert, lookup, h, ↓reduceIte]
  exact lookup_erase_ne m k q h
 theorem lookup_union [DecidableEq K] (a b : FMap K V) (k : K) :
    lookup (union a b) k = match lookup a k with | some v => some v | none => lookup b k := by
  induction a with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨q,v⟩
    by_cases h : k = q
    · subst k; simp [union, lookup]
    · simp only [union, List.foldr_cons, lookup_insert_ne _ _ _ _ h, lookup, h, ↓reduceIte]
      exact ih
end Cjr.FMap

namespace Cjr.LinkedList

/-- The logical abstraction relation reads real object-heap cells. Its inductive
shape rules out cycles and fixes each nonempty node's payload and next pointer. -/
inductive Represents (s : State) : Loc → List Int → Prop where
  | nil : s.obj.lookup (⟨p⟩,0) = some (flag false) → Represents s p []
  | cons : s.obj.lookup (⟨p⟩,0) = some (flag true) →
      s.obj.lookup (⟨p⟩,1) = some (.lit (.int x)) →
      s.obj.lookup (⟨p⟩,2) = some (reference q) →
      Represents s q xs → Represents s p (x :: xs)

/-- Object freshness is the only allocation invariant these operations need.
Other heaps may contain arbitrary caller-owned data. -/
def Bounded (s : State) : Prop := ∀ p i v, s.obj.lookup (⟨p⟩,i) = some v → p < s.next

def Extends (s t : State) : Prop :=
  ∀ p i v, s.obj.lookup (⟨p⟩,i) = some v → t.obj.lookup (⟨p⟩,i) = some v

def Frame (s t : State) : Prop := s.stack = t.stack ∧ s.raw = t.raw ∧ s.blocks = t.blocks

def nodeFields (tag : Bool) (x : Int) (q : Val) : List Val := [flag tag, .lit (.int x), q]
def nodeState (s : State) (tag : Bool) (x : Int) (q : Val) : State :=
  {s with obj := (initFields s.next (nodeFields tag x q) 0).union s.obj, next := s.next + 1}

 theorem extends_refl (s : State) : Extends s s := fun _ _ _ h => h
 theorem extends_trans (h : Extends s t) (h' : Extends t u) : Extends s u :=
  fun p i v hv => h' p i v (h p i v hv)
 theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl⟩
 theorem frame_trans (h : Frame s t) (h' : Frame t u) : Frame s u :=
  ⟨h.1.trans h'.1,h.2.1.trans h'.2.1,h.2.2.trans h'.2.2⟩
 theorem represents_mono (h : Represents s p xs) (he : Extends s t) : Represents t p xs := by
  induction h with
  | nil h => exact .nil (he _ _ _ h)
  | cons h₀ h₁ h₂ _ ih => exact .cons (he _ _ _ h₀) (he _ _ _ h₁) (he _ _ _ h₂) ih
 theorem represents_unique (h : Represents s p xs) (h' : Represents s p ys) : xs = ys := by
  induction h generalizing ys with
  | nil hf => cases h' with
    | nil => rfl
    | cons ht _ _ _ => rw [hf] at ht; simp [flag] at ht
  | cons hf hv hn ht ih => cases h' with
    | nil h => rw [hf] at h; simp [flag] at h
    | cons hf' hv' hn' ht' =>
      have hx := Option.some.inj (hv.symm.trans hv')
      have hp := Option.some.inj (hn.symm.trans hn')
      cases hx; cases hp
      exact congrArg (fun xs => _ :: xs) (ih ht')

 theorem initial_bounded : Bounded stateInit := by
  intro p i v h; exact nomatch h
 theorem wf_bounded (h : StateWF s) : Bounded s := h.objBelow

 theorem initFields_other (o p : Loc) (vs : List Val) (i j : Nat) (h : p ≠ o) :
    (initFields o vs i).lookup (⟨p⟩,j) = none := by
  induction vs generalizing i with
  | nil => rfl
  | cons v vs ih =>
    rw [initFields, FMap.lookup_insert_ne]
    · exact ih _
    · intro he; have := congrArg (fun k : ObjId × Nat => k.1.loc) he; exact h this

 theorem node_lookup_old (s : State) (tag : Bool) (x : Int) (q : Val) (hp : p ≠ s.next) :
    (nodeState s tag x q).obj.lookup (⟨p⟩,i) = s.obj.lookup (⟨p⟩,i) := by
  simp only [nodeState, FMap.lookup_union, initFields_other _ _ _ _ _ hp]
 theorem node_extends (h : Bounded s) : Extends s (nodeState s tag x q) := by
  intro p i v hv
  rw [node_lookup_old]
  · exact hv
  · exact Int.ne_of_lt (h p i v hv)
 theorem node_bounded (h : Bounded s) : Bounded (nodeState s tag x q) := by
  intro p i v hv
  by_cases hp : p = s.next
  · subst p; change s.next < s.next + 1; omega
  · rw [node_lookup_old _ _ _ _ hp] at hv
    change p < s.next + 1
    exact Int.lt_trans (h p i v hv) (by omega)
 theorem node_frame (s : State) : Frame s (nodeState s tag x q) := ⟨rfl,rfl,rfl⟩

 theorem node_tag : (nodeState s tag x q).obj.lookup (⟨s.next⟩,0) = some (flag tag) := by
  simp [nodeState, nodeFields, initFields, FMap.lookup_union]
 theorem node_head : (nodeState s tag x q).obj.lookup (⟨s.next⟩,1) = some (.lit (.int x)) := by
  simp [nodeState, nodeFields, initFields, FMap.lookup_union, FMap.lookup_insert_ne]
 theorem node_tail : (nodeState s tag x q).obj.lookup (⟨s.next⟩,2) = some q := by
  simp [nodeState, nodeFields, initFields, FMap.lookup_union, FMap.lookup_insert_ne]
 theorem nil_rep : Represents (nodeState s false 0 (.lit .unit)) s.next [] := .nil node_tag
 theorem cons_rep (h : Represents s p xs) (hb : Bounded s) :
    Represents (nodeState s true x (reference p)) s.next (x :: xs) :=
  .cons node_tag node_head node_tail (represents_mono h (node_extends hb))

end Cjr.LinkedList
