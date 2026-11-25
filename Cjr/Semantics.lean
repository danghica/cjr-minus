import Cjr.HeadStep
namespace Cjr

inductive CtxItem where
  | letCtx (x : Binder) (body : Expr)
  | varBindCtx (x : String) (body : Expr)
  | popCtx (l : StackId)
  | assignCtx (x : String)
  | stackLoadCtx 
  | stackAssignL (rhs : Expr)
  | stackAssignR (v : Val)
  | stackFieldL (i : Nat) (rhs : Expr)
  | stackFieldR (v : Val) (i : Nat)
  | appL (arg : Expr)
  | appR (v : Val)
  | ifCtx (yes no : Expr)
  | seqCtx (rhs : Expr)
  | binOpL (op : BinOp) (rhs : Expr)
  | binOpR (op : BinOp) (v : Val)
  | allocCtx 
  | freeCtx 
  | loadCtx 
  | storeL (rhs : Expr)
  | storeR (v : Val)
  | offsetL (rhs : Expr)
  | offsetR (v : Val)
  | structCtx (vs : List Val) (es : List Expr)
  | structLoadCtx (i : Nat)
  | structStoreCtx (x : String) (i : Nat)
  | newCtx (vs : List Val) (es : List Expr)
  | fieldLoadCtx (i : Nat)
  | fieldStoreL (i : Nat) (rhs : Expr)
  | fieldStoreR (v : Val) (i : Nat)
  deriving Repr

def fillItem (k : CtxItem) (e : Expr) : Expr :=
  match k with
  | .letCtx x body => .letE x e body
  | .varBindCtx x body => .varBind x e body
  | .popCtx l => .pop l e
  | .assignCtx x => .assign x e
  | .stackLoadCtx  => .stackLoad e
  | .stackAssignL rhs => .stackAssign e rhs
  | .stackAssignR v => .stackAssign (.val v) e
  | .stackFieldL i rhs => .stackFieldStore e i rhs
  | .stackFieldR v i => .stackFieldStore (.val v) i e
  | .appL arg => .app e arg
  | .appR v => .app (.val v) e
  | .ifCtx yes no => .ifE e yes no
  | .seqCtx rhs => .seq e rhs
  | .binOpL op rhs => .binOp op e rhs
  | .binOpR op v => .binOp op (.val v) e
  | .allocCtx  => .alloc e
  | .freeCtx  => .free e
  | .loadCtx  => .load e
  | .storeL rhs => .store e rhs
  | .storeR v => .store (.val v) e
  | .offsetL rhs => .offset e rhs
  | .offsetR v => .offset (.val v) e
  | .structCtx vs es => .struct vs (e :: es)
  | .structLoadCtx i => .structLoad e i
  | .structStoreCtx x i => .structStore x i e
  | .newCtx vs es => .new vs (e :: es)
  | .fieldLoadCtx i => .fieldLoad e i
  | .fieldStoreL i rhs => .fieldStore e i rhs
  | .fieldStoreR v i => .fieldStore (.val v) i e

/-- Frames are stored outermost first. -/
def fill : List CtxItem → Expr → Expr
  | [], e => e
  | k :: ks, e => fillItem k (fill ks e)

def descend (k : CtxItem) (d : List CtxItem × Expr) : List CtxItem × Expr :=
  (k :: d.1, d.2)

/-- Canonical left-to-right evaluation-context decomposition. A value in the
next position is consumed by a head rule, rather than descending into it. -/
def decompose (e : Expr) : List CtxItem × Expr :=
  match e with
  | .letE x a b => match a with
    | .val _ => ([], e)
    | _ => descend (.letCtx x b) (decompose a)
  | .varBind x a b => match a with
    | .val _ => ([], e)
    | _ => descend (.varBindCtx x b) (decompose a)
  | .pop l a => match a with
    | .val _ => ([], e)
    | _ => descend (.popCtx l) (decompose a)
  | .assign x a => match a with
    | .val _ => ([], e)
    | _ => descend (.assignCtx x) (decompose a)
  | .stackLoad a => match a with
    | .val _ => ([], e)
    | _ => descend (.stackLoadCtx) (decompose a)
  | .ifE a b c => match a with
    | .val _ => ([], e)
    | _ => descend (.ifCtx b c) (decompose a)
  | .seq a b => match a with
    | .val _ => ([], e)
    | _ => descend (.seqCtx b) (decompose a)
  | .alloc a => match a with
    | .val _ => ([], e)
    | _ => descend (.allocCtx) (decompose a)
  | .free a => match a with
    | .val _ => ([], e)
    | _ => descend (.freeCtx) (decompose a)
  | .load a => match a with
    | .val _ => ([], e)
    | _ => descend (.loadCtx) (decompose a)
  | .structLoad a i => match a with
    | .val _ => ([], e)
    | _ => descend (.structLoadCtx i) (decompose a)
  | .structStore x i a => match a with
    | .val _ => ([], e)
    | _ => descend (.structStoreCtx x i) (decompose a)
  | .fieldLoad a i => match a with
    | .val _ => ([], e)
    | _ => descend (.fieldLoadCtx i) (decompose a)
  | .app a b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.appR v) (decompose b)
    | _ => descend (.appL b) (decompose a)
  | .stackAssign a b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.stackAssignR v) (decompose b)
    | _ => descend (.stackAssignL b) (decompose a)
  | .stackFieldStore a i b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.stackFieldR v i) (decompose b)
    | _ => descend (.stackFieldL i b) (decompose a)
  | .binOp op a b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.binOpR op v) (decompose b)
    | _ => descend (.binOpL op b) (decompose a)
  | .store a b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.storeR v) (decompose b)
    | _ => descend (.storeL b) (decompose a)
  | .offset a b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.offsetR v) (decompose b)
    | _ => descend (.offsetL b) (decompose a)
  | .fieldStore a i b => match a with
    | .val v => match b with
      | .val _ => ([], e)
      | _ => descend (.fieldStoreR v i) (decompose b)
    | _ => descend (.fieldStoreL i b) (decompose a)
  | .struct vs (a :: es) => match a with
    | .val _ => ([], e)
    | _ => descend (.structCtx vs es) (decompose a)
  | .new vs (a :: es) => match a with
    | .val _ => ([], e)
    | _ => descend (.newCtx vs es) (decompose a)
  | _ => ([], e)

def step (e : Expr) (s : State) : Option (Expr × State) := do
  let (ks, redex) := decompose e
  let (e', s') ← baseStep redex s
  return (fill ks e', s')

/-- Small-step semantics with the canonical evaluation contexts made explicit. -/
def Step (e : Expr) (s : State) (e' : Expr) (s' : State) : Prop :=
  step e s = some (e', s')

/-- Independent contextual closure of head reduction, without an Iris language interface. -/
inductive ContextualStep : Expr → State → Expr → State → Prop where
  | head : BaseStep e s e' s' → ContextualStep e s e' s'
  | under (k : CtxItem) : ContextualStep e s e' s' →
      ContextualStep (fillItem k e) s (fillItem k e') s'

theorem step_deterministic (h₁ : Step e s e₁ s₁) (h₂ : Step e s e₂ s₂) :
    e₁ = e₂ ∧ s₁ = s₂ := by
  exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

@[simp] theorem fillItem_not_value (k : CtxItem) (e : Expr) : toVal (fillItem k e) = none := by
  cases k <;> rfl
@[simp] theorem value_stuck (v : Val) (s : State) : step (.val v) s = none := rfl

/-- Reflexive transitive closure, constructed directly. -/
inductive Steps : Expr → State → Expr → State → Prop where
  | refl : Steps e s e s
  | cons : Step e s e₁ s₁ → Steps e₁ s₁ e₂ s₂ → Steps e s e₂ s₂

inductive RunResult where
  | done (v : Val) (s : State)
  | stuck (e : Expr) (s : State)
  | timeout (e : Expr) (s : State)
  deriving Repr

/-- Fuel limits execution only; it is not part of the small-step semantics. -/
def run : Nat → Expr → State → RunResult
  | 0, e, s => match toVal e with
    | some v => .done v s
    | none => .timeout e s
  | fuel+1, e, s => match toVal e with
    | some v => .done v s
    | none => match step e s with
      | none => .stuck e s
      | some (e', s') => run fuel e' s'
end Cjr
