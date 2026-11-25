import Std

namespace Cjr

abbrev Loc := Int
abbrev Binder := Option String
structure StackId where
  loc : Loc
  deriving DecidableEq, Repr
structure RawId where
  loc : Loc
  deriving DecidableEq, Repr
structure ObjId where
  loc : Loc
  deriving DecidableEq, Repr

inductive Ty where
  | int | float | bool | unit
  | struct (fields : List Ty)
  | ptr (target : Ty)
  | obj (nfields : Nat)
  | fn (arg result : Ty)
  deriving Repr

inductive Lit where
  | int (n : Int) | float (n : Int) | bool (b : Bool) | unit
  | ptr (l : Loc) | null | obj (o : Loc) | stack (l : Loc)
  deriving DecidableEq, Repr
inductive BinOp where
  | plus | minus | mul | div | rem | le | eq | and | bitXor | bitAnd
  deriving DecidableEq, Repr

mutual
inductive Val where
  | lit (l : Lit)
  | recE (f x : Binder) (body : Expr)
  | struct (fields : List Val)
  deriving Repr, BEq
inductive Expr where
  | val (v : Val)
  | var (x : String)
  | recE (f x : Binder) (body : Expr)
  | app (fn arg : Expr)
  | letE (x : Binder) (init body : Expr)
  | varBind (x : String) (init body : Expr)
  | assign (x : String) (rhs : Expr)
  | pop (l : StackId) (body : Expr)
  | stackLoad (e : Expr)
  | stackAssign (lhs rhs : Expr)
  | stackFieldStore (lhs : Expr) (i : Nat) (rhs : Expr)
  | ifE (cond yes no : Expr)
  | whileE (cond body : Expr)
  | seq (first second : Expr)
  | binOp (op : BinOp) (lhs rhs : Expr)
  | alloc (n : Expr) | free (p : Expr) | load (p : Expr)
  | store (p value : Expr) | offset (p index : Expr)
  | struct (done : List Val) (todo : List Expr)
  | structLoad (e : Expr) (i : Nat)
  | structStore (x : String) (i : Nat) (rhs : Expr)
  | new (done : List Val) (todo : List Expr)
  | fieldLoad (e : Expr) (i : Nat)
  | fieldStore (obj : Expr) (i : Nat) (rhs : Expr)
  deriving Repr, BEq
end

def toVal : Expr → Option Val
  | .val v => some v
  | _ => none

def binds (x : String) (b : Binder) : Bool := b == some x

/-- A single traversal implements both upstream substitutions. Immutable substitution
leaves assignment targets alone; mutable substitution rewrites them to stack operations. -/
inductive Replacement where
  | immutable (v : Val)
  | mutable (l : Loc)

def replacementExpr : Replacement → Expr
  | .immutable v => .val v
  | .mutable l => .stackLoad (.val (.lit (.stack l)))

mutual
 def substitute (x : String) (r : Replacement) : Expr → Expr
  | .val v => .val (substituteVal x r v)
  | .var y => if x == y then replacementExpr r else .var y
  | .recE f y e => .recE f y (if binds x f || binds x y then e else substitute x r e)
  | .app a b => .app (substitute x r a) (substitute x r b)
  | .letE b a e => .letE b (substitute x r a) (if binds x b then e else substitute x r e)
  | .varBind y a e => .varBind y (substitute x r a) (if x == y then e else substitute x r e)
  | .assign y e => match r with
    | .mutable l => if x == y then .stackAssign (.val (.lit (.stack l))) (substitute x r e)
                     else .assign y (substitute x r e)
    | .immutable _ => .assign y (substitute x r e)
  | .pop l e => .pop l (substitute x r e)
  | .stackLoad e => .stackLoad (substitute x r e)
  | .stackAssign a b => .stackAssign (substitute x r a) (substitute x r b)
  | .stackFieldStore a i b => .stackFieldStore (substitute x r a) i (substitute x r b)
  | .ifE a b c => .ifE (substitute x r a) (substitute x r b) (substitute x r c)
  | .whileE a b => .whileE (substitute x r a) (substitute x r b)
  | .seq a b => .seq (substitute x r a) (substitute x r b)
  | .binOp op a b => .binOp op (substitute x r a) (substitute x r b)
  | .alloc e => .alloc (substitute x r e)
  | .free e => .free (substitute x r e)
  | .load e => .load (substitute x r e)
  | .store a b => .store (substitute x r a) (substitute x r b)
  | .offset a b => .offset (substitute x r a) (substitute x r b)
  | .struct vs es => .struct (substituteVals x r vs) (substituteExprs x r es)
  | .structLoad e i => .structLoad (substitute x r e) i
  | .structStore y i e => match r with
    | .mutable l => if x == y then .stackFieldStore (.val (.lit (.stack l))) i (substitute x r e)
                     else .structStore y i (substitute x r e)
    | .immutable _ => .structStore y i (substitute x r e)
  | .new vs es => .new (substituteVals x r vs) (substituteExprs x r es)
  | .fieldLoad e i => .fieldLoad (substitute x r e) i
  | .fieldStore a i b => .fieldStore (substitute x r a) i (substitute x r b)
 termination_by structural e => e
 def substituteVal (x : String) (r : Replacement) : Val → Val
  | .lit l => .lit l
  | .recE f y e => .recE f y (if binds x f || binds x y then e else substitute x r e)
  | .struct vs => .struct (substituteVals x r vs)
 termination_by structural w => w
 def substituteVals (x : String) (r : Replacement) : List Val → List Val
  | [] => []
  | v :: vs => substituteVal x r v :: substituteVals x r vs
 termination_by structural vs => vs
 def substituteExprs (x : String) (r : Replacement) : List Expr → List Expr
  | [] => []
  | e :: es => substitute x r e :: substituteExprs x r es
 termination_by structural es => es
end

def subst (x : String) (v : Val) := substitute x (.immutable v)
def substVar (x : String) (l : Loc) := substitute x (.mutable l)
def substBinder (b : Binder) (v : Val) (e : Expr) : Expr :=
  match b with
  | none => e
  | some x => subst x v e

/-- Unbounded two's-complement operations, using the complement encoding
`Int.negSucc n = ~n`. Lean's natural-number bit operations supply the finite bits. -/
def intXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
def intAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .negSucc a, .negSucc b => .negSucc (a ||| b)
  | .ofNat a, .negSucc b => .ofNat (a - (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b - (a &&& b))

def binOpEval : BinOp → Val → Val → Option Val
  | .plus, .lit (.int a), .lit (.int b) => some (.lit (.int (a + b)))
  | .minus, .lit (.int a), .lit (.int b) => some (.lit (.int (a - b)))
  | .mul, .lit (.int a), .lit (.int b) => some (.lit (.int (a * b)))
  | .div, .lit (.int a), .lit (.int b) => if b == 0 then none else some (.lit (.int (a.tdiv b)))
  | .rem, .lit (.int a), .lit (.int b) => if b == 0 then none else some (.lit (.int (a.tmod b)))
  | .bitXor, .lit (.int a), .lit (.int b) => some (.lit (.int (intXor a b)))
  | .bitAnd, .lit (.int a), .lit (.int b) => some (.lit (.int (intAnd a b)))
  | .le, .lit (.int a), .lit (.int b) => some (.lit (.bool (a ≤ b)))
  | .eq, .lit (.int a), .lit (.int b) => some (.lit (.bool (a == b)))
  | .and, .lit (.bool a), .lit (.bool b) => some (.lit (.bool (a && b)))
  | _, _, _ => none

@[simp] theorem toVal_val (v : Val) : toVal (.val v) = some v := rfl
 theorem of_toVal {e : Expr} {v : Val} (h : toVal e = some v) : e = .val v := by
  cases e <;> simp_all [toVal]
end Cjr
