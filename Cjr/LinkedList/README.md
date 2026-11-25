# Persistent linked lists, verified against CJR execution

This module implements singly linked lists of unbounded mathematical integers
using the existing CJR object heap. All traversals are recursive CJR functions;
Lean lists appear only in specifications, proofs, and input fixtures.
No Iris or separation-logic framework is used.

## Code and representation

A `ListNode` has fields `nonempty : Bool`, `value : Int64`, and `next : ListNode`
in the generated Cangjie. In CJR these are field indices 0, 1, and 2. An empty
sentinel has tag false; a nonempty node has tag true, an integer payload, and an
object reference to its tail. The sentinel's remaining fields are outside the
abstract interface. Head and tail require a nonempty list.

`Code.lean` defines `empty`, `cons`, `head`, `tail`, `isEmpty`, `lengthFn`,
`appendFn`, `reverseAuxFn`, `reverse`, and callable constructor/observer/reverse
wrappers. `ofList` constructs input fixtures through CJR allocations and lets;
it is not used to implement traversal. Append copies the first list's spine and
shares the second. Reverse prepends into an accumulator. Existing nodes are
never changed. These are persistent lists: no operation destroys an input or
frees a node. CJR's object heap has no deallocation rule.

`Represents s p xs` in `Heap.lean` is an inductive predicate over actual heap
lookups. It states that reference `p` represents mathematical sequence `xs` in
state `s`:

- For `[]`, field 0 contains false.
- For `x :: xs`, field 0 contains true, field 1 contains integer `x`, field 2
  contains reference `q`, and `Represents s q xs` holds.

This inductive shape describes finite acyclic spines. `represents_unique` proves
that one reference in one heap cannot represent two different sequences. Lists
may share tails, and append/reverse accept aliased inputs.

The allocation precondition `Bounded s` requires existing object locations to
be strictly below `s.next`. It follows from `StateWF s` and holds initially.
A successful operation returns `Preserves s t`, establishing:

- `Bounded t`;
- every pre-existing object-heap lookup remains valid with exactly the same value;
- stack, raw-memory, and block maps are exactly unchanged.

Thus the proofs cover nonempty caller-owned heaps, not just `stateInit`.

## Operational correctness

`Evaluates e s v t` is an abbreviation for the existing `Steps e s (.val v) t`.
Each step uses the executable `step` function in `Cjr/Semantics.lean`.
`Cjr/Execution.lean` proves context lifting and evaluation composition from that
function; it does not introduce a new evaluator or postulate evaluation rules.

`Correctness.lean` proves the following contracts for arbitrary finite represented
lists and all states satisfying the stated preconditions:

- `empty_correct` and `cons_correct`: node construction executes the CJR allocation
  rules. `nil_rep` and `cons_rep` establish the resulting abstraction relation.
- `head_correct`, `tail_correct`, `isEmpty_correct`: observers return the specified
  payload, tail representation, or emptiness Boolean, leaving the entire state
  unchanged. Head/tail use the nonempty precondition.
- `length_correct`: traversal returns `xs.length` and leaves the entire state
  unchanged.
- `append_correct`: two represented lists `xs` and `ys` yield a represented list
  `xs ++ ys`, with `Preserves` for the resulting state.
- `reverseAux_correct`: represented inputs `xs` and `ys` yield
  `xs.reverse ++ ys`, with `Preserves`.
- `reverse_correct`: a represented input `xs` yields `xs.reverse`, with `Preserves`.
- `ofList_correct`: CJR construction terminates with the requested contents.
- `consCall_correct`, `headCall_correct`, `tailCall_correct`,
  `isEmptyCall_correct`, and `reverseCall_correct`: callable wrappers used by
  extraction execute the same proved operations.

The recursion proofs use induction on the arbitrary represented input sequence.
There is no fixed length limit or assumed execution-fuel bound.

## Algebraic specification

`Algebra.lean` lifts the contracts to list-producing CJR expressions. `Models s e
xs` means that in every bounded object-heap extension of `s`, the **actual CJR
expression** `e` terminates with a representation of `xs` and preserves the
caller's heap. Quantification over extensions makes nested operations composable.
`Measures s e n` is the corresponding integer-valued observation.

The public combinators `consExpr`, `appendExpr`, `reverseExpr`, and `lengthExpr`
build ordinary CJR ASTs. Their arguments execute left to right through the same
operational semantics. The following algebraic laws are proved:

- `append_empty_left`, `append_empty_right`: `[] ++ xs = xs = xs ++ []`.
- `append_associative`: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`.
- `reverse_empty`: `reverse [] = []`.
- `reverse_involutive`: `reverse (reverse xs) = xs`.
- `reverse_append`: `reverse (xs ++ ys) = reverse ys ++ reverse xs`.
- `reverse_cons`: `reverse (x :: xs) = reverse xs ++ [x]`.
- `length_empty`: `length [] = 0`.
- `length_cons`: `length (x :: xs) = length xs + 1`.
- `length_append`: `length (xs ++ ys) = length xs + length ys`.
- `length_reverse`: `length (reverse xs) = length xs`.
- `head_cons`, `tail_cons`: `head (x :: xs) = x`, `tail (x :: xs) = xs`.

These are specifications of executed CJR programs, obtained by composing the
operational correctness theorems with sequence identities. They are not merely
proofs about Lean's `List` operations. Equality here is equality of contents
through `Represents`; it does not assert equality of allocation addresses or
final heaps, or contextual equivalence under arbitrary destructive field writes.

`models_terminate` connects the laws to `run`: some finite fuel executes the
program successfully. `models_all_results` uses deterministic CJR reduction to
show every completed execution satisfies the contract. `models_no_stuck` proves
that every finite irreducible execution ends in the specified list value.
`Cjr.evaluates_unique` rules out different results or final states from the same
initial program and state.

## Run, export, and check

From the project root with the pinned Lean toolchain:

```sh
sh scripts/check.sh
lake exe test-linked-list
lake exe cjr --emit linked_list linked_list.cj
python3 tests/native_printer.py
```

The native tests require Cangjie 1.0.5 and run after the printer and linked-list
execution tests have emitted their sources. `generated/cangjie/linked_list.cj`
contains the generated implementation. `Export.lean` supplies signatures and
layout metadata to the existing printer and uses the proved function bodies.

The execution regressions include empty/singleton/negative/repeated-element
inputs, 49 pairs for append and reverse laws, 147 associativity triples, and
nonempty stack/raw/block frames. Native tests compile and run the emitted program
unchanged and with an assertion main checking observers, length, append,
associativity, reverse involution/distribution, and persistence of input lists.

Lean kernel-checks the general correctness proofs and algebraic laws; native
execution is additional validation. Extraction to Cangjie is not a verified
compiler. In particular, the CJR model uses unbounded integers while native
payloads and lengths use `Int64`. Head/tail on an empty sentinel are outside the
specified API; the native printer's nullable self-field convention is relevant
only to the sentinel's otherwise unobserved tail.
