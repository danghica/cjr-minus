import NotMonotone
open Cjr Cjr.Voting

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Independent functional oracle: filter each ranking, then count its head. -/
private def reference (ballots : List (List Nat)) : Nat → List Nat → Int
  | 0, _ => -1
  | fuel+1, active => Id.run do
    let choices := ballots.filterMap (fun b => b.find? active.contains)
    if choices.isEmpty then return -1
    let counts := active.map (fun c => (c, choices.count c))
    if let some (winner,_) := counts.find? (fun (_,v) => 2*v > choices.length) then
      return winner
    let loser := counts.foldl (fun a b =>
      if b.2 < a.2 || (b.2 == a.2 && b.1 > a.1) then b else a)
      (0,choices.length+1)
    return reference ballots fuel (active.filter (· != loser.1))

private def test (n : Nat) (ballots : List (List Nat)) (expected : Int) : IO Unit := do
  let .ok e := election n ballots | throw (IO.userError "unexpected validation failure")
  match run 1000000 e stateInit with
  | .done (.lit (.int actual)) s =>
    check s!"wrong winner: {ballots}: expected {expected}, got {actual}" (actual == expected)
    check "temporary memory leaked" (s.raw.isEmpty && s.blocks.isEmpty && s.stack.isEmpty && s.obj.isEmpty)
    for a in List.range n do
      for b in List.range n do
        if unanimousAbove ballots a b then
          check s!"Pareto violation: everyone prefers {a} to {b}" (actual != (b : Int))
  | _ => throw (IO.userError s!"execution failed for {ballots}")

private def testSwaps (n : Nat) (bs : List (List Nat)) : IO Nat := do
  let mut checked := 0
  for i in List.range bs.length do
    for j in List.range bs.length do
      let swapped := (bs.set i bs[j]!).set j bs[i]!
      match election n bs, election n swapped with
      | .ok e, .ok f => check "swapping voters changed the generated CJR term" (e == f)
      | .error a, .error b => check "swapping voters changed validation" (a == b)
      | _, _ => throw (IO.userError "swapping voters changed validation success")
      checked := checked + 1
  return checked

private def testParetoGuard : IO Unit := do
  let bs := [[0,1,2],[1,0,2]]
  check "A above omitted B counts as strict preference" (unanimousAbove [[0],[0,1]] 0 2)
  check "omitting both gives no strict preference" (!unanimousAbove [[],[0,1]] 0 2)
  check "empty electorate gives no strict unanimity" (!unanimousAbove [] 0 1)
  check "A above B is strict" (!unanimousAbove bs 0 0)
  check "dominated candidate removed" (paretoCandidates 3 bs == [0,1])
  -- Inject incorrect core results to check the guard itself is effective.
  for (raw,expected) in ([(0,0),(1,1),(2,-1),(99,-1),(-2,-1)] : List (Int × Int)) do
    match run 1000 (paretoGuard 3 bs (.val (.lit (.int raw)))) stateInit with
    | .done (.lit (.int actual)) s =>
      check "guard rejected an eligible or accepted a dominated result" (actual == expected)
      check "guard changed machine state" (s.next == 0 && s.raw.isEmpty && s.stack.isEmpty && s.obj.isEmpty)
    | _ => throw (IO.userError "guard did not finish")

def main : IO Unit := do
  testParetoGuard
  test 3 MonotonicityCounterexample.original 0
  test 3 MonotonicityCounterexample.raised 1
  test 0 [] (-1)
  test 3 [] (-1)
  test 3 [[],[]] (-1)
  test 1 [[0],[]] 0
  test 3 [[0],[0],[1],[2]] 0 -- Exactly half is not a majority; transfer rounds required.
  test 3 [[0,1],[0,1],[1,0],[2,1],[2,1]] 0 -- tied minimum 1 eliminated first
  test 3 [[0],[0],[0],[1],[1],[2,1],[2,1]] 1 -- transfer elects 1
  test 3 [[0],[1],[2]] 0 -- deterministic elimination tie
  test 3 [[0],[1],[1],[2]] 1 -- exhausted ballots change denominator
  test 3 [[2],[],[]] 2 -- zero-vote candidates
  check "reject duplicate rankings" (match election 3 [[0,0]] with | .error _ => true | _ => false)
  check "reject unknown candidate" (match election 3 [[3]] with | .error _ => true | _ => false)
  check "reject ballots without candidates" (match election 0 [[0]] with | .error _ => true | _ => false)
  -- All partial rankings of three candidates, every ordered profile up to 2 ballots.
  let rankings : List (List Nat) := [[],[0],[1],[2],[0,1],[0,2],[1,0],[1,2],
    [2,0],[2,1],[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
  let profiles := [[]] ++ rankings.map (fun b => [b]) ++
    rankings.flatMap (fun a => rankings.map (fun b => [a,b]))
  for bs in profiles do test 3 bs (reference bs 3 [0,1,2])
  -- Deterministic broader profiles exercise repeated transfers and unequal tallies.
  for seed in [0:100] do
    let bs := (List.range (3 + seed % 7)).map (fun j =>
      rankings[(seed * 7 + j * 11 + j*j) % rankings.length]!)
    test 3 bs (reference bs 3 [0,1,2])
  for seed in [0:30] do
    let bs := (List.range (seed % 9)).map (fun j =>
      (List.range 5).filter (fun c => (c+j+seed) % 3 != 0) |>.rotateLeft (j % 3))
    test 5 bs (reference bs 5 [0,1,2,3,4])
  let mut swaps := 0
  for bs in [[],[[]],[[0],[1]],[[0],[0],[0],[1],[1],[2,1],[2,1]],
      [[2,1,0],[],[1,0],[0,2],[1,0]],[[3],[0,0],[1]],[[0,0],[3],[]]] do
    swaps := swaps + (← testSwaps 3 bs)
  let .ok demo := election 3 [[0],[0],[0],[1],[1],[2,1],[2,1]]
    | throw (IO.userError "demo validation failed")
  match Cjr.Cangjie.emit (program demo) with
  | .error es => throw (IO.userError (String.intercalate "\n" es))
  | .ok source => IO.FS.writeFile "ranked_choice.cj" source
  let injected := ([(0,0),(1,1),(2,-1),(99,-1),(-2,-1)] : List (Int × Int)).map
    (fun (raw,expected) =>
      (paretoGuard 3 [[0,1,2],[1,0,2]] (.val (.lit (.int raw))),expected))
  let checks := ((demo,1) :: injected).zipIdx.foldr (fun ((expr,expected),i) rest =>
    let name := "checked" ++ toString i
    Expr.letE (some name) expr
      (.ifE (.binOp .eq (.var name) (.val (.lit (.int expected)))) rest (.val (.lit (.int 1)))))
    (.val (.lit (.int 0)))
  match Cjr.Cangjie.emit (program checks) with
  | .error es => throw (IO.userError (String.intercalate "\n" es))
  | .ok source => IO.FS.writeFile "pareto_checks.cj" source
  let .ok before := election 3 MonotonicityCounterexample.original
    | throw (IO.userError "original counterexample failed validation")
  let .ok after := election 3 MonotonicityCounterexample.raised
    | throw (IO.userError "raised counterexample failed validation")
  let monoChecks := Expr.letE (some "before") before
    (.letE (some "after") after
      (.ifE (.binOp .and
        (.binOp .eq (.var "before") (.val (.lit (.int 0))))
        (.binOp .eq (.var "after") (.val (.lit (.int 1)))))
        (.val (.lit (.int 0))) (.val (.lit (.int 1)))))
  match Cjr.Cangjie.emit (program monoChecks) with
  | .error es => throw (IO.userError (String.intercalate "\n" es))
  | .ok source => IO.FS.writeFile "monotonicity_checks.cj" source
  IO.println s!"Passed {profiles.length + 140} CJR executions, input validation, memory cleanup, and checked Cangjie emission."
  IO.println s!"Passed {swaps} voter-swap checks, including repeated/empty ballots and invalid profiles."
  IO.println "Passed Pareto checks for every election, partial-ranking rules, and five injected guard results."
  IO.println "Verified two additional CJR counterexample executions: raising winner 0 makes candidate 1 win."
