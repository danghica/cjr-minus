import Cjr.Cangjie.Environment

namespace Cjr.Cangjie

def nl : String := "\n"
def comma (xs : List String) : String := String.intercalate ", " xs
def catAll (xs : List String) : String := String.join xs
def unsupported (what : String) : String := "/* unsupported: " ++ what ++ " */"
def sym : BinOp → String
  | .plus => " + " | .minus => " - " | .mul => " * " | .div => " / " | .rem => " % "
  | .le => " <= " | .eq => " == " | .and => " && " | .bitXor => " ^ " | .bitAnd => " & "
def lit : Lit → String
  | .int n => toString n
  | .float n => toString n ++ ".0"
  | .bool true => "true" | .bool false => "false" | .unit => "()"
  | .null => "CPointer<Int64>()"
  | .ptr _ => unsupported "raw address literal"
  | .obj _ => unsupported "object reference literal"
  | .stack _ => unsupported "stack slot"
def lam (ind body : String) : String := "{ =>\n" ++ ind ++ "    " ++ body ++ "\n" ++ ind ++ "}()"
def paren (s : String) : String := "(" ++ s ++ ")"
def argIndent (ind : String) (e : Expr) : String := if isStmt e then ind ++ "    " else ind
/-- These wrappers take an already recursively rendered child, keeping the printer structurally total. -/
def asArg (ind : String) (e : Expr) (text : String) : String := if isStmt e then lam ind text else text
def operandIndent (ind : String) (e : Expr) : String := if isBinOp e then ind else argIndent ind e
def asOperand (ind : String) (e : Expr) (text : String) : String :=
  if isBinOp e then paren text else asArg ind e text

def optionTag (vs : List Val) (es : List Expr) : Option Bool :=
  match vs,es with
  | .lit (.bool b) :: _,_ => some b
  | [],.val (.lit (.bool b)) :: _ => some b
  | _,_ => none

def optionNoneUnit (vs : List Val) (es : List Expr) : Bool :=
  match vs,es with
  | [.lit (.bool false),.lit .unit],[] => true
  | [.lit (.bool false)],[.val (.lit .unit)] => true
  | [],[.val (.lit (.bool false)),.val (.lit .unit)] => true
  | _,_ => false

def optionSource (tag : Option Bool) (noneUnit : Bool) (args : List String) : String :=
  match tag,args with
  | some false,[_,_] => if noneUnit then "None" else unsupported "native None requires a unit payload"
  | some true,[_,v] => "Some(" ++ v ++ ")"
  | _,_ => unsupported "native option requires a literal tag and exactly two fields"

def optionProjection (source : String) (i : Nat) : String :=
  match i with
  | 0 => paren source ++ ".isSome()"
  | 1 => paren source ++ ".getOrThrow()"
  | _ => unsupported "native option field index"

def callTarget (env : Env) : Expr → Option Fn
  | .recE _ _ body | .val (.recE _ _ body) => findBody env body
  | .var x => (assoc x env.aliases).bind (findName env)
  | _ => none

def copySource (env : Env) (ind : String) : String :=
  let ind2 := ind ++ "    "
  "if (0 < " ++ varName env "len" ++ ") {\n" ++ ind2 ++ "unsafe {\n" ++
  ind2 ++ "    memmove(CPointer<Unit>(" ++ varName env "dst" ++ " + " ++ varName env "doff" ++
  "), CPointer<Unit>(" ++ varName env "src" ++ " + " ++ varName env "soff" ++
  "), UIntNative(" ++ varName env "len" ++ ") * UIntNative(8))\n" ++
  ind2 ++ "    ()\n" ++ ind2 ++ "}\n" ++ ind ++ "}"

mutual
/-- Layout-directed legacy CJR printer. It preserves the upstream formatting and
unsupported markers. Use `emit` when unsupported terms must be rejected. -/
def ex (env : Env) (ind : String) (e : Expr) : String :=
  let ind2 := ind ++ "    "
  match findClosed env e with
  | some k => k.name ++ "()"
  | none => match e with
    | .val v => exv env ind v
    | .var x => varName env x
    | .recE f x body => match findBody env body with
      | some k => k.name
      | none => match f with
        | none => "{ " ++ binderName x ++ " => " ++ ex env ind body ++ " }"
        | some _ => unsupported "recursive closure"
    | .app f a =>
      let k := callTarget env f
      let args := match _ha : a with
        | .struct vs es => exvs env ind vs ++ exargs env ind es
        | .val (.struct vs) => exvs env ind vs
        | .val (.lit .unit) => []
        | .var x => (assoc x env.pack).getD [varName env x]
        | _ => [asArg ind a (ex env (argIndent ind a) a)]
      match k with
      | some k => match k.owner, args with
        | some _, o :: rest => o ++ "." ++ k.name ++ "(" ++ comma rest ++ ")"
        | _, _ => k.name ++ "(" ++ comma args ++ ")"
      | none =>
        let callee := match _hf : f with
          | .var _ | .structLoad (.var _) _ | .fieldLoad (.var _) _ => ex env ind f
          | _ => paren (ex env ind f)
        callee ++ "(" ++ comma args ++ ")"
    | .letE (some x) e₁ e₂ => match _h₁ : e₁ with
      | .recE none _ body => match findBody env body with
        | some k => ex (withAlias env x k.name) ind e₂
        | none => "let " ++ sanitize x ++ " = " ++ ex env ind e₁ ++ nl ++ ind ++
            ex (withTy env x "") ind e₂
      | .struct vs es =>
        if immediatePack env x e₂ then
          ex (withPack env x (exvs env ind vs ++ exargs env ind es)) ind e₂
        else match declByArity env.sty (vs.length + es.length) with
        | some d => "let " ++ sanitize x ++ " = " ++ ex env ind e₁ ++ nl ++ ind ++
            ex (withTy env x d.name) ind e₂
        | none => ex (withPack env x (exvs env ind vs ++ exargs env ind es)) ind e₂
      | _ => "let " ++ sanitize x ++ " = " ++ asArg ind e₁ (ex env (argIndent ind e₁) e₁) ++
          nl ++ ind ++ ex (withTyOpt env x (classOf env e₁)) ind e₂
    | .letE none a b | .seq a b => ex env ind a ++ nl ++ ind ++ ex env ind b
    | .varBind x a b =>
      if env.bulkCopy && x == "i" && a == .val (.lit (.int 0)) && bulkCopyLoop env.copyRules b
      then copySource env ind
      else "var " ++ sanitize x ++ " = " ++ asArg ind a (ex env (argIndent ind a) a) ++
        nl ++ ind ++ ex (withTyOpt env x (classOf env a)) ind b
    | .assign x a => varName env x ++ " = " ++ asArg ind a (ex env (argIndent ind a) a)
    | .ifE c a b =>
      if simple a && simple b then
        "if (" ++ ex env ind c ++ ") { " ++ ex env ind a ++ " } else { " ++ ex env ind b ++ " }"
      else if isUnit b then
        "if (" ++ ex env ind c ++ ") {\n" ++ ind2 ++ ex env ind2 a ++ nl ++ ind ++ "}"
      else "if (" ++ ex env ind c ++ ") {\n" ++ ind2 ++ ex env ind2 a ++ nl ++ ind ++
        "} else {\n" ++ ind2 ++ ex env ind2 b ++ nl ++ ind ++ "}"
    | .whileE c b => "while (" ++ ex env ind c ++ ") {\n" ++ ind2 ++ ex env ind2 b ++ nl ++ ind ++ "}"
    | .binOp .and a b =>
      if env.strictAnd then
        "({ cjrLeft: Bool, cjrRight: Bool => cjrLeft && cjrRight })(" ++
        asArg ind a (ex env (argIndent ind a) a) ++ ", " ++
        asArg ind b (ex env (argIndent ind b) b) ++ ")"
      else asOperand ind a (ex env (operandIndent ind a) a) ++ sym .and ++
        asOperand ind b (ex env (operandIndent ind b) b)
    | .binOp op a b => asOperand ind a (ex env (operandIndent ind a) a) ++ sym op ++
        asOperand ind b (ex env (operandIndent ind b) b)
    | .alloc n => "unsafe { CPointer<Int64>(calloc(UIntNative(" ++ ex env ind n ++ "), UIntNative(8))) }"
    | .free p => "unsafe { free(CPointer<Unit>(" ++ ex env ind p ++ ")) }"
    | .load (.offset b i) => "unsafe { (" ++ ex env ind b ++ " + " ++
        asOperand ind i (ex env (operandIndent ind i) i) ++ ").read() }"
    | .load (.var x) => "unsafe { " ++ varName env x ++ ".read() }"
    | .load p => "unsafe { (" ++ ex env ind p ++ ").read() }"
    | .store (.offset b i) v => "unsafe { (" ++ ex env ind b ++ " + " ++
        asOperand ind i (ex env (operandIndent ind i) i) ++ ").write(" ++
        asArg ind v (ex env (argIndent ind v) v) ++ ") }"
    | .store (.var x) v => "unsafe { " ++ varName env x ++ ".write(" ++
        asArg ind v (ex env (argIndent ind v) v) ++ ") }"
    | .store p v => "unsafe { (" ++ ex env ind p ++ ").write(" ++
        asArg ind v (ex env (argIndent ind v) v) ++ ") }"
    | .offset b i => "unsafe { " ++ ex env ind b ++ " + " ++
        asOperand ind i (ex env (operandIndent ind i) i) ++ " }"
    | .struct vs es =>
      let args := exvs env ind vs ++ exargs env ind es
      match declByArity env.sty args.length with
      | some d => if (assoc d.name env.nativeOptions).isSome then
          optionSource (optionTag vs es) (optionNoneUnit vs es) args
        else d.name ++ "(" ++ comma args ++ ")"
      | none => "(" ++ comma args ++ ")"
    | .structLoad (.var x) i => match varClass env x with
      | some c => if (assoc c env.nativeOptions).isSome then optionProjection (varName env x) i
          else varName env x ++ "." ++ fieldOf env (some c) i
      | none => varName env x ++ "[" ++ toString i ++ "]"
    | .structLoad s i =>
      match classOf env s with
      | some c => if (assoc c env.nativeOptions).isSome then
          optionProjection ("({ cjrOption: " ++ nativeTy env c ++ " => cjrOption })(" ++ ex env ind s ++ ")") i
        else paren (ex env ind s) ++ "[" ++ toString i ++ "]"
      | none => paren (ex env ind s) ++ "[" ++ toString i ++ "]"
    | .structStore x i a =>
      if ((varClass env x).bind (fun c => assoc c env.nativeOptions)).isSome then
        unsupported "native option field mutation"
      else varName env x ++ "." ++ fieldOf env (varClass env x) i ++
        " = " ++ asArg ind a (ex env (argIndent ind a) a)
    | .new vs es =>
      let items := exvItems env ind vs ++ exItems env ind es
      match declByArity env.cls items.length with
      | some d => d.name ++ "(" ++ comma (ctorArgs d 0 items) ++ ")"
      | none => unsupported "object of unknown layout"
    | .fieldLoad (.var x) i => varName env x ++ "." ++ fieldOf env (varClass env x) i
    | .fieldLoad s i => paren (ex env ind s) ++ "." ++ fieldOf env (classOf env s) i
    | .fieldStore (.var x) i a => varName env x ++ "." ++ fieldOf env (varClass env x) i ++
        " = " ++ asArg ind a (ex env (argIndent ind a) a)
    | .fieldStore s i a => paren (ex env ind s) ++ "." ++ fieldOf env (classOf env s) i ++
        " = " ++ asArg ind a (ex env (argIndent ind a) a)
    | .pop _ _ | .stackLoad _ | .stackAssign _ _ | .stackFieldStore _ _ _ => unsupported "stack form"
termination_by sizeOf e

def exv (env : Env) (ind : String) (v : Val) : String :=
  match v with
  | .lit l => lit l
  | .recE f x body => match findBody env body with
    | some k => k.name
    | none => match f with
      | none => "{ " ++ binderName x ++ " => " ++ ex env ind body ++ " }"
      | some _ => unsupported "recursive closure"
  | .struct vs =>
    let args := exvs env ind vs
    match declByArity env.sty args.length with
    | some d => if (assoc d.name env.nativeOptions).isSome then
        optionSource (optionTag vs []) (optionNoneUnit vs []) args
      else d.name ++ "(" ++ comma args ++ ")"
    | none => "(" ++ comma args ++ ")"
termination_by sizeOf v

def exvs (env : Env) (ind : String) (vs : List Val) : List String :=
  match vs with
  | [] => []
  | v :: vs => exv env ind v :: exvs env ind vs
termination_by sizeOf vs

def exargs (env : Env) (ind : String) (es : List Expr) : List String :=
  match es with
  | [] => []
  | e :: es => asArg ind e (ex env (argIndent ind e) e) :: exargs env ind es
termination_by sizeOf es

def exvItems (env : Env) (ind : String) (vs : List Val) : List (Bool × String) :=
  match vs with
  | [] => []
  | v :: vs => (valIsUnit v, exv env ind v) :: exvItems env ind vs
termination_by sizeOf vs

def exItems (env : Env) (ind : String) (es : List Expr) : List (Bool × String) :=
  match es with
  | [] => []
  | e :: es => (isUnit e, asArg ind e (ex env (argIndent ind e) e)) :: exItems env ind es
termination_by sizeOf es
end

def fnParts (k : Fn) : Option String × List String × Expr :=
  match k.arg with
  | none => (none, [], k.body)
  | some b => match peel b k.body, k.owner with
    | ([], _), some _ => (some b, [], k.body)
    | ([], _), none => (none, [b], k.body)
    | (x :: xs, r), some _ => (some x, xs, r)
    | (xs, r), none => (none, xs, r)

def printFn (env : Env) (ind : String) (k : Fn) : String :=
  let (recv, ps, body) := fnParts k
  let typed := ps.zip k.tys
  let env1 := typed.foldl (fun env (x,t) => withTy env x t) (withThis (without env k.name) recv k.owner)
  let env2 := {env1 with bulkCopy := bulkCopyMethod env1.copyRules k.body, currentFn := some (k.name,k.ret)}
  let ind2 := ind ++ "    "
  let kw := if k.owner.isSome then "public func " else "func "
  ind ++ kw ++ k.name ++ "(" ++ comma (typed.map (fun (x,t) => sanitize x ++ ": " ++ nativeTy env t)) ++
    "): " ++ nativeTy env k.ret ++ " {\n" ++ ind2 ++ ex env2 ind2 body ++ nl ++ ind ++ "}\n"

def ownedBy (c : String) (k : Fn) : Bool := k.owner == some c
def selfField (kw : String) (d : Decl) (t : String) : Bool := kw == "class" && t == d.name
def printOneField (kw : String) (d : Decl) (f t : String) : String :=
  if selfField kw d t then
    "    var " ++ f ++ "_raw: ?" ++ t ++ nl ++
    "    public mut prop " ++ f ++ ": " ++ t ++ " {\n" ++
    "        get() {\n" ++ "            match (this." ++ f ++ "_raw) {\n" ++
    "                case Some(n) => n\n" ++ "                case None => this\n" ++
    "            }\n        }\n" ++ "        set(n) { this." ++ f ++ "_raw = n }\n    }\n"
  else "    public var " ++ f ++ ": " ++ t ++ nl

def ctorParam (kw : String) (d : Decl) (f t : String) : String :=
  f ++ ": " ++ if selfField kw d t then "?" ++ t else t
def initStore (kw : String) (d : Decl) (f t : String) : String :=
  "        this." ++ (if selfField kw d t then f ++ "_raw" else f) ++ " = " ++ f ++ nl

def printDecl (env : Env) (kw : String) (d : Decl) : String :=
  let d := {d with fields := d.fields.map (fun (f,t) => (f,nativeTy env t))}
  kw ++ " " ++ d.name ++ " {\n" ++
  catAll (d.fields.map (fun (f,t) => printOneField kw d f t)) ++
  "    public init(" ++ comma (d.fields.map (fun (f,t) => ctorParam kw d f t)) ++ ") {\n" ++
  catAll (d.fields.map (fun (f,t) => initStore kw d f t)) ++ "    }\n" ++
  catAll ((env.fns.filter (ownedBy d.name)).map (fun k => nl ++ printFn env "    " k)) ++ "}\n"

def prelude : String :=
  "// Generated by Cjr.Cangjie from the CJR core terms.\n\n" ++
  "foreign func calloc(count: UIntNative, size: UIntNative): CPointer<Unit>\n" ++
  "foreign func free(ptr: CPointer<Unit>): Unit\n"

def printProgUsing (strictAnd : Bool) (rules : CopyRules) (p : Prog) : String :=
  let env : Env := {cls := p.classes, sty := p.structs, fns := p.fns, copyRules := rules, strictAnd := strictAnd, nativeOptions := p.nativeOptions}
  prelude ++
  (if p.fns.any (fun k => bulkCopyMethod rules k.body) then
    "foreign func memmove(dst: CPointer<Unit>, src: CPointer<Unit>, size: UIntNative): CPointer<Unit>\n" else "") ++
  catAll ((p.structs.filter (fun d => (assoc d.name p.nativeOptions).isNone)).map (fun d => nl ++ printDecl env "struct" d)) ++
  catAll (p.classes.map (fun d => nl ++ printDecl env "class" d)) ++
  catAll ((p.fns.filter (·.owner.isNone)).map (fun k => nl ++ printFn env "" k)) ++
  "\nmain(): Unit {\n    " ++ ex env "    " p.main ++ "\n}\n"
def printProgWith (rules : CopyRules) (p : Prog) : String := printProgUsing false rules p
def printProg (p : Prog) : String := printProgWith {} p
end Cjr.Cangjie
