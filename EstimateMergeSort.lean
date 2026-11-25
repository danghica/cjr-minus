import Cjr
open Cjr.LinkedList.MergeSort

def main (args : List String) : IO Unit := do
  let [text] := args | throw (IO.userError "Usage: lake exe estimate-mergesort N")
  let some n := text.toNat? | throw (IO.userError "N must be a nonnegative integer")
  IO.println s!"Input length: {n}"
  IO.println s!"Safe worst-case budget: {worstBudget n} CJR reductions"
  IO.println s!"Proved lower bound: {15*n*n.log2} CJR reductions"
  IO.println s!"Ceiling log2: {ceilLog n}"
  IO.println "Includes sorting an existing list; excludes input construction."
  IO.println "One CJR transition counts as one reduction; this is not a CPU-time estimate."
