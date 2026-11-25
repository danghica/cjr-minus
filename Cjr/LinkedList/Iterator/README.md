# A stateful list iterator

`iterator(list)` creates a `ListIterator` with two members: `list` retains the
original list root, and `cursor` initially points to that root. Its `next()`
method returns a native Cangjie `?ListNode`:

- On a nonempty cursor, it saves the current node, moves `cursor` to that node's
  next link, and returns `Some(savedNode)`.
- At the empty sentinel, it returns `None` and changes nothing. Every subsequent
  call continues returning `None`.

The iterator returns the existing node, not a copy or just its integer payload.
It never changes a list node and does not allocate during `next` in CJR. Multiple
iterators over the same list have independent cursors. Direct writes to iterator
members or list links are outside the interface's invariant.

## Operational implementation and specification

`Code.lean` contains the CJR constructor and method bodies. The result is encoded
in the existing core syntax as `[true, nodeReference]` for Some and `[false, ()]`
for None; no reduction rule or new language primitive is introduced.

`Heap.lean` defines `RepresentsIterator s it root full remaining`. The iterator's
actual heap fields retain `root` and a cursor representing `remaining`.
`remaining` is a suffix of `full`. Both list spines are protected by their
allocation order: every list node precedes the iterator's address, so updating
its cursor cannot modify a list node. Constructor correctness establishes this
invariant from the existing linked-list representation and allocation bound.

`Correctness.lean` proves:

- `create_correct`: construction retains the original root, initializes the
  cursor to it, and preserves the old heap.
- `next_some`: for `remaining = x :: xs`, the actual CJR call returns the current
  node, updates the cursor to exactly its tail, and re-establishes the invariant
  for `xs`. The returned node still represents `x :: xs` after the update.
- `next_none`: an exhausted iterator returns None in exactly the same state.
- `exhausted_repeat`: any finite number of further calls remains a no-op.
- `iterate_correct`: successive operational calls yield the entire remaining
  sequence in order and reach the exhausted invariant, then return None.
- `iterate_exhausted`: a complete traversal is followed by another stable None.
- `next_terminates`: some finite interpreter fuel suffices for every valid call.

The evaluation judgments are the existing executable `Steps` relation.
`CursorFrame` states that every object field except `(iterator, cursor)` is
unchanged, as are the stack, raw heap, block map, and allocation counter. This is
stronger and more precise than a contents-only frame for this mutable operation.
Proofs cover arbitrary finite lists and valid states, not only the test inputs.

## Cangjie output and checks

`Export.lean` emits a real `ListIterator.next(): ?ListNode` method and a one-argument
`iterator(list)` factory. The underlying generated class also has its usual
explicit two-field constructor. Use the factory to establish the invariant.

The printer's opt-in `nativeOptions` metadata maps the tagged core structure
`NodeOption` to native `?ListNode`, constructors to `Some`/`None`, and guarded
projections to `isSome()`/`getOrThrow()`. The absent payload must be literal unit
so lowering to None cannot discard a payload computation. Invalid mappings and
unsupported construction/mutation forms are rejected. Unwrapping is intended
only after testing Some; the None payload is not part of the public interface.
Existing printing without native-option metadata is unchanged.

```sh
lake exe test-iterator
lake exe cjr --emit list_iterator list_iterator.cj
sh scripts/check.sh
python3 tests/native_printer.py
```

The generated file is `generated/cangjie/list_iterator.cj`. Tests cover empty,
singleton, multi-node, negative, and repeated-value lists; exact returned node
identity; one-link advances; no repeated nodes; preservation of all other object
fields; repeated exhaustion; and independent iterators. The native Cangjie 1.0.5
harness checks the generated method, option operations, traversal order, retained
list, exhaustion, and independent cursors. General correctness is kernel-checked
in Lean; extraction remains runtime-validated rather than a proved compiler.
