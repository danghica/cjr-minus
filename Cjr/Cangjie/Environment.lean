import Cjr.Syntax

/-! Layout-directed printing metadata, ported from upstream `cj_print.v`.
Types are supplied by the caller because the operational language is untyped. -/
namespace Cjr.Cangjie

structure Decl where
  name : String
  fields : List (String × String)
  deriving Repr, BEq
structure Fn where
  name : String
  owner : Option String := none
  arg : Binder := none
  body : Expr
  tys : List String := []
  ret : String := "Unit"
  deriving Repr
structure Prog where
  classes : List Decl := []
  structs : List Decl := []
  fns : List Fn := []
  main : Expr := .val (.lit .unit)
  nativeOptions : List (String × String) := []
  deriving Repr

/-- Explicit, opt-in repository-specific native copy rewrites. Disabled by default. -/
structure CopyRules where
  methods : List Expr := []
  loop : Option Expr := none
  deriving Repr
structure Env where
  cls : List Decl := []
  sty : List Decl := []
  fns : List Fn := []
  this : Option String := none
  ty : List (String × String) := []
  pack : List (String × List String) := []
  aliases : List (String × String) := []
  currentFn : Option (String × String) := none
  strictAnd : Bool := false
  bulkCopy : Bool := false
  copyRules : CopyRules := {}
  nativeOptions : List (String × String) := []
  deriving Repr

def assoc (k : String) : List (String × α) → Option α
  | [] => none
  | (y, a) :: xs => if k == y then some a else assoc k xs

/-- Explicit native representation of a tagged two-field CJR option structure. -/
def nativeTy (env : Env) (t : String) : String :=
  match assoc t env.nativeOptions with | some payload => "?" ++ payload | none => t

def declByName (ds : List Decl) (n : String) : Option Decl := ds.find? (·.name == n)
def declByArity (ds : List Decl) (n : Nat) : Option Decl := ds.find? (·.fields.length == n)
def allDecls (env : Env) : List Decl := env.cls ++ env.sty
def findBody (env : Env) (b : Expr) : Option Fn := env.fns.find? (·.body == b)
def findName (env : Env) (n : String) : Option Fn := env.fns.find? (·.name == n)
def findClosed (env : Env) (e : Expr) : Option Fn :=
  env.fns.find? (fun k => k.arg.isNone && k.body == e)
def withTy (env : Env) (x t : String) : Env := {env with ty := (x,t) :: env.ty}
def withTyOpt (env : Env) (x : String) (t : Option String) : Env := withTy env x (t.getD "")
def withPack (env : Env) (x : String) (ss : List String) : Env := {env with pack := (x,ss) :: env.pack}
def withAlias (env : Env) (x n : String) : Env := {env with aliases := (x,n) :: env.aliases}
def withThis (env : Env) (r owner : Option String) : Env :=
  {env with this := r, ty := match r, owner with
    | some r, some c => (r,c) :: env.ty
    | _, _ => env.ty}
def without (env : Env) (n : String) : Env := {env with fns := env.fns.filter (·.name != n)}
def bulkCopyMethod (rules : CopyRules) (body : Expr) : Bool := rules.methods.any (· == body)
def bulkCopyLoop (rules : CopyRules) (body : Expr) : Bool :=
  match rules.loop with | some e => e == body | none => false

def keywords : List String :=
  ["this", "super", "init", "main", "func", "let", "var", "type", "in", "is", "as",
   "where", "match", "case", "class", "struct", "spawn", "true", "false", "if", "else",
   "while", "for", "do", "return", "break", "continue"]
def sanitize (x : String) : String :=
  if x == "this" then "self" else if keywords.contains x then x ++ "_" else x
def binderName (b : Binder) : String := b.map sanitize |>.getD "_"
def varName (env : Env) (x : String) : String :=
  if env.this == some x then "this" else (assoc x env.aliases).getD (sanitize x)
def fieldOf (env : Env) (c : Option String) (i : Nat) : String :=
  ((c.bind (declByName (allDecls env))).bind (fun d => d.fields[i]?)).map Prod.fst
    |>.getD ("f" ++ toString i)
def fieldTy (env : Env) (c : Option String) (i : Nat) : Option String := do
  let d ← c.bind (declByName (allDecls env))
  let (_, t) ← d.fields[i]?
  let _ ← declByName (allDecls env) t
  return t
def varClass (env : Env) (x : String) : Option String := do
  let t ← assoc x env.ty
  let _ ← declByName (allDecls env) t
  return t

def classOf (env : Env) : Expr → Option String
  | .var x => varClass env x
  | .new vs es => (declByArity env.cls (vs.length + es.length)).map Decl.name
  | .struct vs es => (declByArity env.sty (vs.length + es.length)).map Decl.name
  | .val (.struct vs) => (declByArity env.sty vs.length).map Decl.name
  | .fieldLoad (.var y) i | .structLoad (.var y) i => fieldTy env (varClass env y) i
  | .app (.recE _ _ b) _ | .app (.val (.recE _ _ b)) _ => do
      let k ← findBody env b
      let _ ← declByName (allDecls env) k.ret
      return k.ret
  | .app (.var x) _ => do
      let ret ← match assoc x env.aliases with
        | some n => (findName env n).map Fn.ret
        | none => match env.currentFn with
          | some (n,t) => if x == n then some t else none
          | none => none
      let _ ← declByName (allDecls env) ret
      return ret
  | _ => none

def immediatePack (env : Env) (x : String) (e : Expr) : Bool :=
  let call := match e with | .letE _ a _ => a | _ => e
  match call with
  | .app (.recE _ _ b) (.var y) | .app (.val (.recE _ _ b)) (.var y) =>
      x == y && (findBody env b).isSome
  | _ => false

def isStmt : Expr → Bool
  | .letE _ _ _ | .varBind _ _ _ | .seq _ _ | .whileE _ _ => true
  | _ => false
def isBinOp : Expr → Bool | .binOp _ _ _ => true | _ => false
def isUnit : Expr → Bool | .val (.lit .unit) => true | _ => false
def valIsUnit : Val → Bool | .lit .unit => true | _ => false
def leaf : Expr → Bool
  | .val (.lit _) | .var _ | .fieldLoad (.var _) _ | .structLoad (.var _) _ => true
  | _ => false
def simple : Expr → Bool | .binOp _ a b => leaf a && leaf b | e => leaf e

def ctorArgs (d : Decl) : Nat → List (Bool × String) → List String
  | _, [] => []
  | i, (u,s) :: rest =>
    let s' := match d.fields[i]? with
      | some (_,t) => if u && t == d.name then "None" else s
      | none => s
    s' :: ctorArgs d (i+1) rest

/-- Peel argument-pack projections in the same order as the upstream printer. -/
def peel (b : String) (e : Expr) : List String × Expr :=
  match e with
  | .letE (some x) (.structLoad (.var y) _) e₂ =>
    if y == b then let (xs,r) := peel b e₂; (x :: xs,r) else ([],e)
  | _ => ([],e)

end Cjr.Cangjie
