import Cjr.Cangjie.Printer
import Cjr.Cangjie.Transform

namespace Cjr.Cangjie

def identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha && c.toNat < 128 || c == '_') &&
      cs.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_')) &&
      !(keywords ++ ["public", "private", "foreign", "static"]).contains s

def duplicates (names : List String) : List String :=
  match names with
  | [] => []
  | n :: ns => (if ns.contains n then ["duplicate name: " ++ n] else []) ++ duplicates ns

def checkProg (p : Prog) : List String := Id.run do
  let mut errors := duplicates ((p.classes ++ p.structs).map Decl.name)
  errors := errors ++ duplicates (p.fns.map (fun k => (k.owner.getD "") ++ "." ++ k.name))
  for d in p.classes ++ p.structs do
    if !identifier d.name then errors := errors ++ ["invalid layout name: " ++ d.name]
    errors := errors ++ duplicates (d.fields.map Prod.fst)
    for (f,t) in d.fields do
      if !identifier f then errors := errors ++ ["invalid field name: " ++ f]
      if t.isEmpty then errors := errors ++ ["empty field type: " ++ d.name ++ "." ++ f]
  errors := errors ++ duplicates (p.nativeOptions.map Prod.fst)
  for (name,payload) in p.nativeOptions do
    match declByName p.structs name with
    | none => errors := errors ++ ["native option needs a declared structure: " ++ name]
    | some d =>
      match d.fields with
      | [(_,"Bool"),(_,t)] =>
        if t != payload then errors := errors ++ ["native option payload mismatch: " ++ name]
      | _ => errors := errors ++ ["native option needs Bool tag and payload fields: " ++ name]
    if (declByName (p.classes ++ p.structs) payload).isNone then
      errors := errors ++ ["native option payload needs a declared type: " ++ payload]
  for k in p.fns do
    if !identifier k.name then errors := errors ++ ["invalid function name: " ++ k.name]
    if k.ret.isEmpty || k.tys.any String.isEmpty then errors := errors ++ ["empty signature type: " ++ k.name]
    let (recv,ps,_) := fnParts k
    if ps.length != k.tys.length then errors := errors ++ ["parameter/type arity mismatch: " ++ k.name]
    errors := errors ++ duplicates (ps.map sanitize)
    if (recv.toList ++ ps).any (fun n => !(identifier (sanitize n))) then
      errors := errors ++ ["invalid parameter name: " ++ k.name]
    match k.owner with
    | some c =>
      if (declByName (p.classes ++ p.structs) c).isNone then errors := errors ++ ["unknown method owner: " ++ c]
      if recv.isNone then errors := errors ++ ["method has no receiver: " ++ k.name]
    | none => pure ()
  return errors

/-- Checked source emission: validates basic metadata and refuses upstream's
unsupported markers. This is not a Cangjie type checker. Strict conjunction is
rendered through a two-argument lambda so both operands execute, as in CJR. -/
def emit (p : Prog) (rules : CopyRules := {}) : Except (List String) String :=
  let errors := checkProg p
  let source := printProgUsing true rules p
  let markers := (source.splitOn "/* unsupported: ").drop 1
    |>.map (fun s => "unsupported: " ++ ((s.splitOn " */").head!))
  match errors ++ markers with
  | [] => .ok source
  | errors => .error errors

theorem emit_metadata_checked (h : emit p rules = .ok source) : checkProg p = [] := by
  unfold emit at h
  dsimp only at h
  split at h
  next he =>
    cases hc : checkProg p with
    | nil => rfl
    | cons a as => simp [hc] at he
  next => contradiction
end Cjr.Cangjie
