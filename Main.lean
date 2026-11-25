import Cjr
open Cjr Cjr.Examples

def demo : IO Unit := do
  for (name, program) in [
    ("factorial(5)", .app factorial (int 5)),
    ("mutable counter", counter),
    ("raw memory round trip", rawRoundTrip),
    ("object fields", objectRoundTrip),
    ("mutable struct", structRoundTrip)] do
    match run 200 program stateInit with
    | .done v s => IO.println s!"{name}: {repr v}; next={s.next}, stack={s.stack.length}, raw={s.raw.length}, blocks={s.blocks.length}, fields={s.obj.length}"
    | .stuck e _ => throw (IO.userError s!"{name}: stuck at {repr e}")
    | .timeout _ _ => throw (IO.userError s!"{name}: exhausted fuel")

def printablePrograms : List (String × Cjr.Cangjie.Prog) :=
  Cjr.Cangjie.Examples.programs ++ [("linked_list",Cjr.LinkedList.program),("list_iterator",Cjr.LinkedList.Iterator.program),("mergesort",Cjr.LinkedList.MergeSort.program)]

/-- Emit a complete named sample to stdout or a .cj file. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] => demo
  | ["--list"] =>
    for (name, _) in printablePrograms do IO.println name
  | "--emit" :: name :: rest =>
    let some (_, p) := printablePrograms.find? (·.1 == name)
      | throw (IO.userError s!"Unknown program: {name}. Use --list.")
    let source ← match Cjr.Cangjie.emit p with
      | .ok s => pure s
      | .error errors => throw (IO.userError (String.intercalate "\n" errors))
    match rest with
    | [] => IO.print source
    | [path] => IO.FS.writeFile path source
    | _ => throw (IO.userError "Usage: cjr --emit NAME [OUTPUT.cj]")
  | _ => throw (IO.userError "Usage: cjr [--list | --emit NAME [OUTPUT.cj]]")
