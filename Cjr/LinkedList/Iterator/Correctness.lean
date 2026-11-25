import Cjr.LinkedList.Iterator.Heap
namespace Cjr.LinkedList.Iterator
open Evaluates

theorem create_exec (s : State) (p : Loc) : Evaluates (create p) s (reference s.next) (created s p) :=
  new_nil _ _
theorem createCall_exec (s : State) (p : Loc) :
    Evaluates (createCall p) s (reference s.next) (created s p) := by
  apply Steps.cons (show Step (createCall p) s
    (substBinder (some "list") (reference p) createBody) s from rfl)
  exact new_cons (value _ _) (new_cons (value _ _) (new_nil _ _))

theorem create_correct (hp : Represents s p xs) (hb : Bounded s) :
    Evaluates (createCall p) s (reference s.next) (created s p) ∧
    RepresentsIterator (created s p) s.next p xs xs ∧ Preserves s (created s p) :=
  ⟨createCall_exec _ _,created_rep hp hb,⟨created_bounded hb,created_extends hb,⟨rfl,rfl,rfl⟩⟩⟩

def nextBranch (it p : Loc) : Expr :=
  .ifE (.fieldLoad (refExpr p) 0)
    (.seq (.fieldStore (refExpr it) 1 (.fieldLoad (refExpr p) 2))
      (.struct [flag true] [refExpr p])) (.val (optionNode none))

theorem next_unfold (hc : s.obj.lookup (⟨it⟩,1) = some (reference p)) :
    Steps (next it) s (nextBranch it p) s := by
  apply Steps.cons (show Step (next it) s (substBinder (some "self") (reference it) nextBody) s from rfl)
  apply steps_trans (steps_under (.letCtx (some "p") _) (field (value _ _) hc))
  exact .cons (by rfl) .refl

/-- Exhaustion is a no-op, and the original list and terminal cursor remain valid. -/
theorem next_none (h : RepresentsIterator s it root full []) :
    Evaluates (next it) s (optionNode none) s := by
  obtain ⟨p,_,hc,_,hr,_⟩ := h
  cases hr with
  | nil _ hf =>
    apply steps_trans (next_unfold hc)
    exact Evaluates.if_false (field (value _ _) hf) (value _ _)

/-- A successful next returns the actual current node, moves exactly one link,
preserves all nodes and all fields except this iterator's cursor, and consumes
exactly one abstract element. It allocates no memory. -/
theorem next_some (h : RepresentsIterator s it root full (x :: xs)) :
    ∃ p q, Evaluates (next it) s (optionNode (some p)) (advance s it q) ∧
      RepresentsIterator (advance s it q) it root full xs ∧
      Protected (advance s it q) it p (x :: xs) ∧
      CursorFrame s (advance s it q) it := by
  obtain ⟨p,hl,hc,horig,hr,consumed,hfull⟩ := h
  cases hr with
  | @cons _ _ q _ hp hf hv hn ht =>
    refine ⟨p,q,?_,?_,?_,advance_frame _ _ _⟩
    · apply steps_trans (next_unfold hc)
      apply Evaluates.if_true (field (value _ _) hf)
      apply Evaluates.seq (field_store (value _ _) (field (value _ _) hn) hc)
      exact struct_cons (value _ _) (struct_nil _ _)
    · refine ⟨q,?_,?_,horig.advance,ht.advance,consumed ++ [x],?_⟩
      · rw [(advance_frame s it q).other it 0 (by simp)]
        exact hl
      · exact FMap.lookup_insert _ _ _
      · simpa [List.append_assoc] using hfull
    · exact (Protected.cons hp hf hv hn ht).advance

/-- Once exhausted, even repeated next calls return None with exactly the same state. -/
theorem exhausted_stable (h : RepresentsIterator s it root full []) :
    Evaluates (.seq (next it) (next it)) s (optionNode none) s :=
  Evaluates.seq (next_none h) (next_none h)

/-- An iteration trace consists entirely of actual CJR calls. Each successful
call returns a node whose payload is the next sequence element; the final call
returns None. No fuel bound or list-length limit is assumed. -/
inductive Iteration (it : Loc) : State → List Int → State → Prop where
  | done : Evaluates (next it) s (optionNode none) s → Iteration it s [] s
  | step : Evaluates (next it) s (optionNode (some p)) t →
      t.obj.lookup (⟨p⟩,1) = some (.lit (.int x)) →
      Iteration it t xs u → Iteration it s (x :: xs) u

theorem iterate_correct (h : RepresentsIterator s it root full remaining) :
    ∃ t, Iteration it s remaining t ∧ RepresentsIterator t it root full [] ∧ CursorFrame s t it := by
  induction remaining generalizing s with
  | nil => exact ⟨s,.done (next_none h),h,cursorFrame_refl _ _⟩
  | cons x xs ih =>
    obtain ⟨p,q,he,hi,hp,hf⟩ := next_some h
    obtain ⟨t,ht,hi',hf'⟩ := ih hi
    cases hp with
    | cons _ _ hv _ _ => exact ⟨t,.step he hv ht,hi',cursorFrame_trans hf hf'⟩

/-- After the complete ordered traversal the next operation remains exhausted. -/
theorem iterate_exhausted (h : RepresentsIterator s it root full remaining) :
    ∃ t, Iteration it s remaining t ∧ Evaluates (next it) t (optionNode none) t ∧ CursorFrame s t it := by
  obtain ⟨t,he,hi,hf⟩ := iterate_correct h
  exact ⟨t,he,next_none hi,hf⟩

/-- Any number of further calls after exhaustion is a no-op returning None. -/
def repeatNext (it : Loc) : Nat → Expr
  | 0 => .val (optionNode none)
  | n+1 => .seq (next it) (repeatNext it n)

theorem exhausted_repeat (h : RepresentsIterator s it root full []) (n : Nat) :
    Evaluates (repeatNext it n) s (optionNode none) s := by
  induction n with
  | zero => exact value _ _
  | succ n ih => exact Evaluates.seq (next_none h) ih

theorem next_terminates (h : RepresentsIterator s it root full remaining) :
    ∃ fuel v t, run fuel (next it) s = .done v t ∧ CursorFrame s t it := by
  cases remaining with
  | nil =>
    obtain ⟨fuel,hf⟩ := evaluates_run (next_none h)
    exact ⟨fuel,optionNode none,s,hf,cursorFrame_refl _ _⟩
  | cons x xs =>
    obtain ⟨p,q,he,_,_,hf⟩ := next_some h
    obtain ⟨fuel,hrun⟩ := evaluates_run he
    exact ⟨fuel,optionNode (some p),advance s it q,hrun,hf⟩

end Cjr.LinkedList.Iterator
