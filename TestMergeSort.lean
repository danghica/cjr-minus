import Cjr
open Cjr Cjr.LinkedList Cjr.LinkedList.MergeSort

private def check (message : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError ("Mergesort regression failed: " ++ message))
private def execute (e : Expr) (s : State) : IO (Val × State) :=
  match run 1000000 e s with
  | .done v t => pure (v,t)
  | result => throw (IO.userError s!"Execution did not finish: {repr result}")
private def object : Val → IO Loc
  | .lit (.obj p) => pure p
  | _ => throw (IO.userError "expected list node reference")
private def decode : Nat → State → Loc → Option (List Int)
  | 0,_,_ => none
  | n+1,s,p => do
    let .lit (.bool tag) ← s.obj.lookup (⟨p⟩,0) | none
    if !tag then return []
    let .lit (.int x) ← s.obj.lookup (⟨p⟩,1) | none
    let .lit (.obj q) ← s.obj.lookup (⟨p⟩,2) | none
    return x :: (← decode n s q)
private def ordered : List Int → Bool
  | [] => true
  | x :: xs => xs.all (fun y => x ≤ y) && ordered xs
private def permutation (xs ys : List Int) : Bool :=
  xs.length == ys.length && (xs ++ ys).all (fun x => xs.count x == ys.count x)
private def frames (s t : State) : Bool :=
  s.stack == t.stack && s.raw == t.raw && s.blocks == t.blocks &&
    s.obj.all (fun (k,v) => t.obj.lookup k == some v)

private def test (xs : List Int) (initial : State := stateInit) : IO Unit := do
  let (v,s) ← execute (ofList xs) initial
  let p ← object v
  let (result,t) ← execute (sortList p) s
  let r ← object result
  let some output := decode (xs.length+1) t r | throw (IO.userError "invalid sorted list heap")
  check "output in order" (ordered output)
  check "permutation including duplicates" (permutation xs output)
  -- Standard-library sort is only a differential test oracle, not the implementation or proof.
  check "independent reference" (output == xs.mergeSort (· ≤ ·))
  check "input unchanged" (decode (xs.length+1) t p == some xs)
  check "caller heaps and objects unchanged" (frames s t)
  if xs.length ≤ 1 then
    check "empty/singleton fast path" (r == p && t.next == s.next && t.obj == s.obj)
  let (halves,u) ← execute (splitList p) s
  let .struct [.lit (.obj a),.lit (.obj b)] := halves | throw (IO.userError "invalid split pair")
  check "left split" (decode (xs.length+1) u a == some (deal xs).1)
  check "right split" (decode (xs.length+1) u b == some (deal xs).2)
  check "split preserves caller" (frames s u)

private def inputs : Nat → List (List Int)
  | 0 => [[]]
  | n+1 => (inputs n).flatMap (fun xs => [-1,0,1].map (· :: xs))

def main : IO Unit := do
  let exhaustive := (List.range 6).flatMap inputs
  for xs in exhaustive do test xs
  for xs in ([
    [7,-3,2,2,0,-3,8,1], List.range 24 |>.map (fun n => (23-n : Nat)),
    List.replicate 24 4, [-9223372036854775808,9223372036854775807,0,-1,1]] : List (List Int)) do
    test xs
  let framed : State := {stack := [(⟨-2⟩,.lit (.int 11))],raw := [(⟨-10⟩,.lit (.int 9))],blocks := [(⟨-10⟩,1)]}
  test [4,1,4,-2,0] framed
  -- Direct merge is checked independently of the recursive sort.
  let e := .letE (some "a") (ofList [-3,0,2,2])
    (.letE (some "b") (ofList [-3,1,2,9])
      (.app (.val mergeFn) (.struct [] [.var "a",.var "b"])))
  let (v,t) ← execute e stateInit
  let p ← object v
  check "direct merge" (decode 9 t p == some [-3,-3,0,1,2,2,2,9])
  match Cjr.Cangjie.emit Cjr.LinkedList.MergeSort.program with
  | .error errors => throw (IO.userError (String.intercalate "\n" errors))
  | .ok source =>
    IO.FS.createDirAll ".lake/printer-output"
    IO.FS.createDirAll "generated/cangjie"
    IO.FS.writeFile ".lake/printer-output/mergesort.cj" source
    IO.FS.writeFile "generated/cangjie/mergesort.cj" source
  IO.println s!"Mergesort checks passed: {exhaustive.length} exhaustive inputs, negatives, duplicates, boundaries, longer lists, split/merge, caller frames, and Cangjie emission."
