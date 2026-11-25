import Cjr.LinkedList.Iterator.Code

namespace Cjr.LinkedList.Iterator

/-- A protected list spine. Every node precedes the iterator's allocation address,
so changing an iterator field cannot change any node of either retained list. -/
inductive Protected (s : State) (limit : Loc) : Loc → List Int → Prop where
  | nil : p < limit → s.obj.lookup (⟨p⟩,0) = some (flag false) → Protected s limit p []
  | cons : p < limit → s.obj.lookup (⟨p⟩,0) = some (flag true) →
      s.obj.lookup (⟨p⟩,1) = some (.lit (.int x)) →
      s.obj.lookup (⟨p⟩,2) = some (reference q) →
      Protected s limit q xs → Protected s limit p (x :: xs)

namespace Protected
 theorem represents (h : Protected s limit p xs) : Represents s p xs := by
  induction h with
  | nil _ hf => exact .nil hf
  | cons _ hf hv hn _ ih => exact .cons hf hv hn ih
 theorem mono (h : Protected s limit p xs) (he : Extends s t) : Protected t limit p xs := by
  induction h with
  | nil hp hf => exact .nil hp (he _ _ _ hf)
  | cons hp hf hv hn _ ih => exact .cons hp (he _ _ _ hf) (he _ _ _ hv) (he _ _ _ hn) ih
 theorem protect (h : Represents s p xs) (hb : Bounded s) : Protected s s.next p xs := by
  induction h with
  | nil hf => exact .nil (hb _ _ _ hf) hf
  | cons hf hv hn _ ih => exact .cons (hb _ _ _ hf) hf hv hn ih
 theorem advance (h : Protected s it p xs) : Protected (advance s it q) it p xs := by
  have lookup_old : ∀ p j, p < it →
      (Iterator.advance s it q).obj.lookup (⟨p⟩,j) = s.obj.lookup (⟨p⟩,j) := by
    intro p j hp
    apply FMap.lookup_insert_ne
    intro he
    have he' : p = it := congrArg (fun k : ObjId × Nat => k.1.loc) he
    exact (Int.ne_of_lt hp) he'
  induction h with
  | nil hp hf => exact .nil hp (by rw [lookup_old _ _ hp]; exact hf)
  | cons hp hf hv hn _ ih =>
    exact .cons hp (by rw [lookup_old _ _ hp]; exact hf)
      (by rw [lookup_old _ _ hp]; exact hv) (by rw [lookup_old _ _ hp]; exact hn) ih
end Protected

/-- `remaining` is a suffix of `contents`. Both the retained root and the cursor
are checked against actual object fields and protected from cursor mutation. -/
def RepresentsIterator (s : State) (it root : Loc) (contents remaining : List Int) : Prop :=
  ∃ cursor, s.obj.lookup (⟨it⟩,0) = some (reference root) ∧
    s.obj.lookup (⟨it⟩,1) = some (reference cursor) ∧
    Protected s it root contents ∧ Protected s it cursor remaining ∧
    ∃ consumed, contents = consumed ++ remaining

/-- A next call changes at most (iterator, cursor); every other field and all
other heaps, including the fresh counter, are unchanged. -/
structure CursorFrame (s t : State) (it : Loc) : Prop where
  frame : Frame s t
  counter : t.next = s.next
  other : ∀ p j, (ObjId.mk p,j) ≠ (ObjId.mk it,1) → t.obj.lookup (⟨p⟩,j) = s.obj.lookup (⟨p⟩,j)

 theorem cursorFrame_refl (s : State) (it : Loc) : CursorFrame s s it :=
  ⟨frame_refl _,rfl,fun _ _ _ => rfl⟩
 theorem cursorFrame_trans (h : CursorFrame s t it) (h' : CursorFrame t u it) : CursorFrame s u it :=
  ⟨frame_trans h.frame h'.frame,h'.counter.trans h.counter,fun p j hp => (h'.other p j hp).trans (h.other p j hp)⟩
 theorem advance_frame (s : State) (it q : Loc) : CursorFrame s (advance s it q) it :=
  ⟨frame_refl _,rfl,fun _ _ hp => FMap.lookup_insert_ne _ _ _ _ hp⟩

 theorem created_extends (hb : Bounded s) : Extends s (created s p) := by
  intro o j v hv
  have ho : o ≠ s.next := Int.ne_of_lt (hb _ _ _ hv)
  simp only [created,FMap.lookup_union,initFields_other _ _ _ _ _ ho]
  exact hv
 theorem created_bounded (hb : Bounded s) : Bounded (created s p) := by
  intro o j v hv
  by_cases ho : o = s.next
  · subst o; change s.next < s.next+1; omega
  · simp only [created,FMap.lookup_union,initFields_other _ _ _ _ _ ho] at hv
    change o < s.next+1
    exact Int.lt_trans (hb _ _ _ hv) (by omega)
 theorem created_list : (created s p).obj.lookup (⟨s.next⟩,0) = some (reference p) := by
  simp [created,initFields,FMap.lookup_union]
 theorem created_cursor : (created s p).obj.lookup (⟨s.next⟩,1) = some (reference p) := by
  simp [created,initFields,FMap.lookup_union,FMap.lookup_insert_ne]
 theorem created_rep (hp : Represents s p xs) (hb : Bounded s) :
    RepresentsIterator (created s p) s.next p xs xs := by
  have hl := (Protected.protect hp hb).mono (created_extends (p := p) hb)
  exact ⟨p,created_list,created_cursor,hl,hl,⟨[],rfl⟩⟩

 theorem advance_bounded (hb : Bounded s) (hc : s.obj.lookup (⟨it⟩,1) = some (reference old)) :
    Bounded (advance s it q) := by
  intro p j v hv
  by_cases he : (ObjId.mk p,j) = (ObjId.mk it,1)
  · have hp : p = it := congrArg (fun k : ObjId × Nat => k.1.loc) he
    subst p
    exact hb _ _ _ hc
  · rw [(advance_frame s it q).other p j he] at hv
    exact hb _ _ _ hv
end Cjr.LinkedList.Iterator
