import Cjr
open Cjr Cjr.LinkedList

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError ("Linked-list regression failed: " ++ name))

private def decode : Nat → State → Loc → Option (List Int)
  | 0, _, _ => none
  | n+1, s, p => do
    let .lit (.bool tag) ← s.obj.lookup (⟨p⟩,0) | none
    if !tag then return []
    let .lit (.int x) ← s.obj.lookup (⟨p⟩,1) | none
    let .lit (.obj q) ← s.obj.lookup (⟨p⟩,2) | none
    let xs ← decode n s q
    return x :: xs

private def runList (name : String) (e : Expr) (expected : List Int) : IO Unit := do
  match run 100000 e stateInit with
  | .done (.lit (.obj p)) s =>
    check name (decode (expected.length + 1) s p == some expected)
    check (name ++ " frame") (s.raw.isEmpty && s.stack.isEmpty && s.blocks.isEmpty)
  | result => throw (IO.userError s!"{name}: unexpected execution result {repr result}")

private def runInt (name : String) (e : Expr) (expected : Int) : IO Unit := do
  match run 100000 e stateInit with
  | .done (.lit (.int n)) _ => check name (n == expected)
  | result => throw (IO.userError s!"{name}: unexpected execution result {repr result}")

def main : IO Unit := do
  let cases : List (List Int) := [[],[0],[1],[-1,2],[1,2,3],[3,3,3],[-5,0,7,8]]
  for xs in cases do
    let a := ofList xs
    runList "ofList" a xs
    runList "reverse" (reverseExpr a) xs.reverse
    runList "reverse involution" (reverseExpr (reverseExpr a)) xs
    runList "append right identity" (appendExpr a empty) xs
    runList "append left identity" (appendExpr empty a) xs
    runList "tail cons" (.fieldLoad (consExpr 42 a) 2) xs
    runInt "head cons" (.fieldLoad (consExpr 42 a) 1) 42
    runInt "length" (lengthExpr a) xs.length
    runInt "length reverse" (lengthExpr (reverseExpr a)) xs.length
    for ys in cases do
      let b := ofList ys
      runList "append" (appendExpr a b) (xs ++ ys)
      runList "reverse append" (reverseExpr (appendExpr a b)) (ys.reverse ++ xs.reverse)
      runList "append reverses" (appendExpr (reverseExpr b) (reverseExpr a)) (ys.reverse ++ xs.reverse)
      runInt "length append" (lengthExpr (appendExpr a b)) (xs.length + ys.length)
      for zs in ([[],[4],[-2,5]] : List (List Int)) do
        let c := ofList zs
        runList "left associative" (appendExpr (appendExpr a b) c) (xs ++ ys ++ zs)
        runList "right associative" (appendExpr a (appendExpr b c)) (xs ++ ys ++ zs)
  -- Nonempty caller-owned heaps are preserved, not just the initially empty frame.
  let framed : State := {stack := [(⟨-2⟩,.lit (.int 11))], raw := [(⟨-10⟩,.lit (.int 9))], blocks := [(⟨-10⟩,1)]}
  match run 100000 (reverseExpr (appendExpr (ofList [1,2]) (ofList [3]))) framed with
  | .done (.lit (.obj p)) s =>
    check "framed contents" (decode 4 s p == some [3,2,1])
    check "raw frame" (s.raw.lookup ⟨-10⟩ == some (.lit (.int 9)))
    check "stack frame" (s.stack.lookup ⟨-2⟩ == some (.lit (.int 11)))
    check "block frame" (s.blocks.lookup ⟨-10⟩ == some 1)
  | _ => throw (IO.userError "framed list computation did not finish")
  match Cjr.Cangjie.emit program with
  | .error errors => throw (IO.userError (String.intercalate "\n" errors))
  | .ok source =>
    IO.FS.createDirAll ".lake/printer-output"
    IO.FS.createDirAll "generated/cangjie"
    IO.FS.writeFile ".lake/printer-output/linked_list.cj" source
    IO.FS.writeFile "generated/cangjie/linked_list.cj" source
  IO.println "Linked-list checks passed: construction, observers, 49 append/reverse cases, 147 associativity triples, caller heap frames, and Cangjie emission."
