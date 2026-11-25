import Cjr.State
namespace Cjr

def unitExpr : Expr := .val (.lit .unit)

/-- All 25 upstream base-step rules. None denotes absence of a rule, not a runtime exception. -/
def baseStep (e : Expr) (s : State) : Option (Expr × State) :=
  match e with
  -- RecS
  | .recE f x body => some (.val (.recE f x body), s)
  -- AppS
  | .app (.val (.recE f x body)) (.val v) =>
      some (substBinder x v (substBinder f (.recE f x body) body), s)
  -- LetS
  | .letE x (.val v) body => some (substBinder x v body, s)
  -- VarBindS
  | .varBind x (.val v) body =>
      some (.pop ⟨s.next⟩ (substVar x s.next body),
        {s with stack := s.stack.insert ⟨s.next⟩ v, next := s.next + 1})
  -- PopS
  | .pop l (.val v) => some (.val v, {s with stack := s.stack.erase l})
  -- StackLoadS
  | .stackLoad (.val (.lit (.stack l))) => do
      let v ← s.stack.lookup ⟨l⟩
      return (.val v, s)
  -- StackAssignS
  | .stackAssign (.val (.lit (.stack l))) (.val v) => do
      let _ ← s.stack.lookup ⟨l⟩
      return (unitExpr, {s with stack := s.stack.insert ⟨l⟩ v})
  -- StackFieldS
  | .stackFieldStore (.val (.lit (.stack l))) i (.val v) => do
      let .struct vs ← s.stack.lookup ⟨l⟩ | none
      let _ ← vs[i]?
      return (unitExpr, {s with stack := s.stack.insert ⟨l⟩ (.struct (setNth i v vs))})
  -- IfTrueS
  | .ifE (.val (.lit (.bool true))) a _ => some (a, s)
  -- IfFalseS
  | .ifE (.val (.lit (.bool false))) _ b => some (b, s)
  -- WhileS
  | .whileE a b => some (.ifE a (.seq b (.whileE a b)) unitExpr, s)
  -- SeqS
  | .seq (.val _) b => some (b, s)
  -- BinOpS
  | .binOp op (.val a) (.val b) => do
      let v ← binOpEval op a b
      return (.val v, s)
  -- StructStepS
  | .struct vs (.val v :: es) => some (.struct (vs ++ [v]) es, s)
  -- StructDoneS
  | .struct vs [] => some (.val (.struct vs), s)
  -- StructLoadS
  | .structLoad (.val (.struct vs)) i => do
      let v ← vs[i]?
      return (.val v, s)
  -- AllocS
  | .alloc (.val (.lit (.int n))) =>
      if n > 0 then some (.val (.lit (.ptr s.next)),
        {s with raw := (initCells s.next n.toNat).union s.raw,
                blocks := s.blocks.insert ⟨s.next⟩ n.toNat, next := s.next + n})
      else none
  -- FreeS
  | .free (.val (.lit (.ptr l))) => do
      let len ← s.blocks.lookup ⟨l⟩
      return (unitExpr, {s with raw := freeCells l len s.raw, blocks := s.blocks.erase ⟨l⟩})
  -- LoadS
  | .load (.val (.lit (.ptr l))) => do
      let v ← s.raw.lookup ⟨l⟩
      return (.val v, s)
  -- StoreS
  | .store (.val (.lit (.ptr l))) (.val v) => do
      let _ ← s.raw.lookup ⟨l⟩
      return (unitExpr, {s with raw := s.raw.insert ⟨l⟩ v})
  -- OffsetS
  | .offset (.val (.lit (.ptr l))) (.val (.lit (.int i))) => some (.val (.lit (.ptr (l+i))), s)
  -- NewStepS
  | .new vs (.val v :: es) => some (.new (vs ++ [v]) es, s)
  -- NewDoneS
  | .new vs [] => some (.val (.lit (.obj s.next)),
      {s with obj := (initFields s.next vs 0).union s.obj, next := s.next + 1})
  -- FieldLoadS
  | .fieldLoad (.val (.lit (.obj o))) i => do
      let v ← s.obj.lookup (⟨o⟩, i)
      return (.val v, s)
  -- FieldStoreS
  | .fieldStore (.val (.lit (.obj o))) i (.val v) => do
      let _ ← s.obj.lookup (⟨o⟩, i)
      return (unitExpr, {s with obj := s.obj.insert (⟨o⟩, i) v})
  | _ => none

/-- Relational presentation of the executable head rules. Observations and spawned
threads are omitted because every upstream rule produces empty lists for both. -/
def BaseStep (e : Expr) (s : State) (e' : Expr) (s' : State) : Prop :=
  baseStep e s = some (e', s')

theorem baseStep_deterministic (h₁ : BaseStep e s e₁ s₁) (h₂ : BaseStep e s e₂ s₂) :
    e₁ = e₂ ∧ s₁ = s₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  exact Prod.mk.inj h
@[simp] theorem value_base_stuck (v : Val) (s : State) : baseStep (.val v) s = none := rfl
end Cjr
