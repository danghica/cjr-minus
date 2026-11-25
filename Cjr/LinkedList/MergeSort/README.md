# Mergesort, verified against mathematical sorting

This module implements persistent top-down mergesort in the existing CJR linked
list language. `mergeSort(p)` returns an ordered list with exactly the same
integer elements and multiplicities as the input. It does not change the input.

## Independent mathematical specification

`Math.lean` defines:

```lean
def Ordered (xs : List Int) : Prop := xs.Pairwise (· ≤ ·)
def Sorting (input output : List Int) : Prop :=
  Ordered output ∧ output.Perm input
```

`Ordered` requires every earlier element to be at most every later element;
equal adjacent elements are allowed. `List.Perm` is the standard inductive
permutation relation, so no element can be lost, introduced, or duplicated.
`Sorting.count_eq` explicitly derives equality of the occurrence count of every
integer. The specification does not refer to execution, heaps, or mergesort.

The mathematical helpers are a balanced alternating split (`deal`) and a
comparison merge (`merge`). Their proofs establish:

- `deal_perm`: concatenating the halves is a permutation of the original list.
- `deal_lengths`: the halves account for the entire length and differ in length
  by at most one.
- `deal_smaller`: both halves are strictly smaller when input length is at least two.
- `merge_perm`: merging preserves the concatenated input multiset, even when the
  input lists are not ordered.
- `merge_ordered`: merging two ordered lists yields an ordered list.

These helpers and proofs use only Lean's bundled standard library. Neither the
CJR implementation nor its mathematical refinement invokes a library sorting
function. The standard-library sort appears only as an extra runtime test oracle.

## CJR implementation

`Code.lean` constructs actual CJR recursive closures:

- `splitFn` / `splitList`: recurse through the spine and distribute nodes into
  alternating halves, returning a structure containing their references.
- `mergeFn` / `mergeList`: compare heads and prepend the smaller element to a
  recursive merge. A tie selects the left head. An empty argument returns the
  other list.
- `sortFn` / `sortList`: return empty and singleton inputs immediately; otherwise
  split, recursively sort each half, and merge the two sorted lists.
- `sortExpr`: apply mergesort to a CJR expression which computes its input.

The implementation reads object fields and allocates new persistent nodes;
it does not mutate any old node. It uses no new operational primitive, sorting
oracle, list-to-array conversion, or host-language sort. Alternating splitting
is not a claim of stable sorting for records with equal keys; the specified
payload type is Int and correctness is orderedness plus permutation.

## General operational correctness

`Helpers.lean` proves split and merge refinement directly with `Evaluates`, which
is the existing executable small-step `Steps` relation. `split_correct` relates
both returned heap lists to `deal`; `merge_correct` relates the returned heap
list to mathematical `merge` without assuming sorted inputs.

The main theorem in `Correctness.lean` is:

```lean
theorem sort_correct (hp : Represents s p xs) (hb : Bounded s) :
  ∃ output r t,
    Evaluates (sortList p) s (reference r) t ∧
    Represents t r output ∧
    Sorting xs output ∧
    Preserves s t
```

It proves total correctness for arbitrary finite represented inputs and every
state satisfying the allocation invariant. `Preserves` includes preservation of
all pre-existing object cells, exactly unchanged stack/raw/block maps, and a
valid allocation bound in the resulting state. Sharing with other lists or
existing iterators is therefore preserved. Empty and singleton inputs return
the original reference in exactly the original state.

The proof recurses on input length. `deal_smaller` justifies both recursive sort
calls, and merge recurses on the sum of its input lengths. All recursion is
accepted by Lean's termination checker. There is no fixed list-size limit or
assumed execution-fuel bound.

Additional theorems connect the contract to clients and execution:

- `sortExpr_correct`: correctness when the input is itself computed by a CJR program.
- `sort_all_results`: every completed execution satisfies the contract, using
  deterministic reduction rather than assuming one chosen result is representative.
- `sort_terminates`: some finite fuel makes the existing interpreter return a
  represented sorted permutation of the input.
- `sort_no_stuck`: under the preconditions, every finite irreducible execution is
  a successful result satisfying `Sorting`.

## Export and validation

`Export.lean` supplies layouts and signatures to the existing Cangjie printer.
The generated file contains `splitList`, `mergeLists`, and `mergeSort`, using the
same CJR bodies as the proofs. Recursive structure-returning calls retain their
layout metadata so split projections become `parts.left` and `parts.right`.

```sh
sh scripts/check.sh
lake exe test-mergesort
lake exe cjr --emit mergesort mergesort.cj
python3 tests/native_printer.py --only mergesort
```

The generated implementation is `generated/cangjie/mergesort.cj`. The CJR tests
exhaust all 364 inputs of length zero through five over `[-1, 0, 1]`, checking
orderedness, occurrence counts, a differential reference, input preservation,
split results, and caller heap frames. Additional cases cover longer reversed
lists, duplicate-heavy inputs, negative values, Int64 boundaries, and direct merge.
Native Cangjie 1.0.5 tests compile and execute the emitted program and an assertion
main checking sorted contents, duplicates, split/merge, empty/singleton inputs,
longer lists, and preservation of the source list.

The general sorting and operational proofs are kernel-checked Lean theorems,
without admissions, Iris, or added axioms. Native execution is additional testing;
extraction is not a proved compiler. CJR integers are unbounded, while generated
payloads use native Int64. Record stability is not claimed. Exact CJR step counts and logarithmic complexity
bounds are now proved separately; see [COST.md](COST.md).

## Verified complexity

[The step-count proof guide](COST.md) defines the cost unit and derives the bound.
For an existing list of size `n >= 1`, sorting uses at most
`37n(ceil(log2 n)+1)-30` CJR transitions and at least `15n floor(log2 n)`.
The exact counted operational proof establishes Theta(n log n), including a
size-only sufficient interpreter fuel. Use `lake exe estimate-mergesort N`.
