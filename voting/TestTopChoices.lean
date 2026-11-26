import TopChoices
open Cjr Cjr.Voting

private def check (message : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError message)

private def reference (bs : List (List Nat)) : Nat → List Nat → Int
  | 0,_ => -1
  | fuel+1,active => Id.run do
    let votes := bs.filterMap (fun row => row.find? active.contains)
    if votes.isEmpty then return -1
    let counts := active.map (fun c => (c,votes.count c))
    if let some (c,_) := counts.find? (fun (_,v) => 2*v > votes.length) then return c
    let loser := counts.foldl (fun a b => if b.2 < a.2 || (b.2 == a.2 && b.1 > a.1) then b else a)
      (0,votes.length+1)
    return reference bs fuel (active.filter (· != loser.1))

private def topReference (n : Nat) : Nat → List (List Nat) → List Int
  | 0,_ => []
  | k+1,bs =>
    let c := reference bs n (List.range n)
    if c < 0 then [] else c :: topReference n k (bs.map (·.filter (fun x => (x : Int) != c)))

private def decode : Nat → State → Loc → Option (List Int)
  | 0,_,_ => none
  | k+1,s,p => do
    let .lit (.bool nonempty) ← s.obj.lookup (⟨p⟩,0) | none
    if !nonempty then return []
    let .lit (.int c) ← s.obj.lookup (⟨p⟩,1) | none
    let .lit (.obj q) ← s.obj.lookup (⟨p⟩,2) | none
    return c :: (← decode k s q)

private def test (n limit : Nat) (bs : List (List Nat)) : IO Unit := do
  let .ok e := topElection n limit bs | throw (IO.userError "top validation failed")
  match run 2000000 e stateInit with
  | .done (.lit (.obj p)) s =>
    let result := decode (limit+1) s p
    let expected := topReference n limit bs
    check s!"top {limit}: {bs}: expected {expected}, got {result}" (result == some expected)
    check "temporary memory leaked" (s.raw.isEmpty && s.blocks.isEmpty && s.stack.isEmpty)
    check "repeated candidate" (expected.eraseDups.length == expected.length)
  | _ => throw (IO.userError s!"top execution failed for {bs}")

def main : IO Unit := do
  test 0 0 []
  for limit in List.range 4 do
    for bs in ([[],[[]],[[2]],[[0],[1],[2]],[[0],[0],[0],[1],[1],[2,1],[2,1]],
        [[0,1,2],[1,2,0],[2,0,1]],[[2,1,0],[2],[1],[0]],[[0,1],[0,1]]] : List (List (List Nat))) do
      test 3 limit bs
  let rankings : List (List Nat) := [[],[0],[1],[2],[0,1],[0,2],[1,0],[1,2],
    [2,0],[2,1],[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
  for a in rankings do
    for b in rankings do
      for limit in List.range 4 do test 3 limit [a,b]
  check "reject excessive limit" (match topElection 3 4 [] with | .error _ => true | _ => false)
  check "still reject duplicates" (match topElection 3 2 [[0,0]] with | .error _ => true | _ => false)
  let .ok demo := topElection 3 2 [[0],[0],[0],[1],[1],[2,1],[2,1]]
    | throw (IO.userError "invalid top demo")
  match Cjr.Cangjie.emit (topProgram demo) with
  | .error es => throw (IO.userError (String.intercalate "\n" es))
  | .ok source => IO.FS.writeFile "ranked_choice.cj" source
  IO.println "Passed 1057 multi-choice CJR executions against sequential IRV, limits, exhaustion, and raw-memory cleanup."
