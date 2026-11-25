import Cjr
open Cjr Cjr.LinkedList
namespace IteratorTest
open Cjr.LinkedList.Iterator

private def check (message : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError ("Iterator regression failed: " ++ message))
private def execute (e : Expr) (s : State) : IO (Val × State) :=
  match run 100000 e s with
  | .done v t => pure (v,t)
  | result => throw (IO.userError s!"Iterator execution did not finish: {repr result}")
private def object : Val → IO Loc
  | .lit (.obj p) => pure p
  | _ => throw (IO.userError "expected object reference")
private def cursor (s : State) (it : Loc) : IO Loc := do
  let some v := s.obj.lookup (⟨it⟩,1) | throw (IO.userError "missing cursor field")
  object v
private def decode : Nat → State → Loc → Option (List Int)
  | 0,_,_ => none
  | n+1,s,p => do
    let .lit (.bool tag) ← s.obj.lookup (⟨p⟩,0) | none
    if !tag then return []
    let .lit (.int x) ← s.obj.lookup (⟨p⟩,1) | none
    let .lit (.obj q) ← s.obj.lookup (⟨p⟩,2) | none
    return x :: (← decode n s q)

private def testList (xs : List Int) : IO Unit := do
  let (rootValue,s) ← execute (ofList xs) stateInit
  let root ← object rootValue
  let (iteratorValue,t) ← execute (createCall root) s
  let it ← object iteratorValue
  check "list member" (t.obj.lookup (⟨it⟩,0) == some (reference root))
  check "initial cursor" ((← cursor t it) == root)
  let mut state := t
  let mut seen : List Loc := []
  for x in xs do
    let oldCursor ← cursor state it
    let oldTail := state.obj.lookup (⟨oldCursor⟩,2)
    let (result,updated) ← execute (next it) state
    check "returns actual current node" (result == optionNode (some oldCursor))
    check "node value" (updated.obj.lookup (⟨oldCursor⟩,1) == some (.lit (.int x)))
    check "moves one link" (updated.obj.lookup (⟨it⟩,1) == oldTail)
    check "never returns a node twice" (!seen.contains oldCursor)
    seen := oldCursor :: seen
    check "retains original list" (decode (xs.length+1) updated root == some xs)
    check "retains list member" (updated.obj.lookup (⟨it⟩,0) == some (reference root))
    check "no allocation in next" (updated.next == state.next)
    check "all other object fields unchanged"
      (state.obj.all (fun (key,v) => key == (ObjId.mk it,1) || updated.obj.lookup key == some v))
    state := updated
  for _ in [0:4] do
    let (result,updated) ← execute (next it) state
    check "stable None" (result == optionNode none)
    check "exhaustion leaves state unchanged" (updated.obj == state.obj && updated.next == state.next)
    state := updated
  -- Two iterators retain independent cursors over the same shared list.
  let (otherValue,u) ← execute (createCall root) state
  let other ← object otherValue
  let firstCursor ← cursor u it
  let (_,u') ← execute (next other) u
  check "independent iterators" ((← cursor u' it) == firstCursor)
  check "shared original list unchanged" (decode (xs.length+1) u' root == some xs)

private def optionPrinterChecks : IO Unit := do
  let base := Cjr.LinkedList.Iterator.program
  let rejects := fun p => match Cjr.Cangjie.emit p with | .error _ => true | .ok _ => false
  check "reject invalid native option layout"
    (rejects {base with nativeOptions := [("Missing","ListNode")]})
  check "reject absent payload with effects"
    (rejects {base with main := .struct [flag false] [.seq (integer 1) (.val (.lit .unit))]})
  check "reject malformed native option arity"
    (rejects {base with structs := [⟨"NodeOption",[("node","ListNode")]⟩]})

end IteratorTest

def main : IO Unit := do
  for xs in ([[],[1],[1,2,3],[-5,0,7,7],List.replicate 12 9] : List (List Int)) do
    IteratorTest.testList xs
  IteratorTest.optionPrinterChecks
  match Cjr.Cangjie.emit Cjr.LinkedList.Iterator.program with
  | .error errors => throw (IO.userError (String.intercalate "\n" errors))
  | .ok source =>
    IO.FS.createDirAll ".lake/printer-output"
    IO.FS.createDirAll "generated/cangjie"
    IO.FS.writeFile ".lake/printer-output/list_iterator.cj" source
    IO.FS.writeFile "generated/cangjie/list_iterator.cj" source
  IO.println "Iterator checks passed: empty/singleton/multi-node lists, actual node identity, one-link advancement, no repeats, stable exhaustion, independent cursors, and native option printing."
