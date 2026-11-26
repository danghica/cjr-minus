<p align="center">
  <img src="assets/cjr-minus-logo.jpg" alt="cjr− logo: an open black radical with a red horizontal brushstroke above the cjr− wordmark" width="640">
</p>

# CJR operational semantics in Lean

A self-contained Lean 4 reconstruction of the operational semantics in
[`danghica/cjr-core`, `theories/lang.v`](https://github.com/danghica/cjr-core/blob/c663bd896f92d4646901786642af823c6a278bed/theories/lang.v),
pinned to commit `c663bd896f92d4646901786642af823c6a278bed`.
It imports only Lean's bundled `Std`; it uses no Iris, Rocq, stdpp, Mathlib,
external proof framework, admitted proofs, or project-defined axioms.

## Build and run

Install Lean's `elan` toolchain manager, then run in this directory:

```sh
lake build
lake exe cjr
sh scripts/check.sh
```

`lean-toolchain` pins Lean 4.24.0. Lake obtains that compiler when necessary;
there are no third-party package dependencies. `lake build` checks the proofs
and the example equalities as part of building the library. The executable
prints five sample executions. `scripts/check.sh` also reports theorem axioms.

## Implementation

- `Cjr/Syntax.lean`: all 26 expression forms, mutually defined values, intended
  monomorphic types, all 10 binary operators, and both substitutions. The
  substitutions recurse through closures and aggregate values, respect
  shadowing, and distinguish immutable bindings from mutable stack slots.
- `Cjr/State.lean`: finite maps built from association lists, distinct stack/raw/
  object identifiers, the four maps and shared integer allocation counter,
  block and field initialization, freeing, and the six `StateWF` clauses.
- `Cjr/HeadStep.lean`: all 25 upstream head rules, with the upstream rule names
  next to their Lean counterparts. `baseStep` is executable; `BaseStep` is its
  relational graph.
- `Cjr/Semantics.lean`: all 29 evaluation-context items, filling, left-to-right
  decomposition, executable `step`, its relational graph `Step`, an independent
  inductive contextual closure `ContextualStep`, multi-step reduction, and a
  fuel-bounded interpreter distinguishing completion, stuckness, and timeout.
- `Cjr/Properties.lean`: machine-checked context reconstruction and decomposition,
  deterministic stepping, soundness of executable steps for the independent
  contextual relation, and soundness of completed interpreter runs for both
  multi-step relations.
- `Cjr/Examples.lean`: 47 kernel-checked execution and edge-case regressions, plus a
  semantic derivation for factorial of five.
- `Cjr/Cangjie/`: the Cangjie printer, layouts/signatures, placeholder-pointer
  restoration, checked emission, and example programs.
- `upstream.json`: source commit and SHA-256, rule correspondence, and printer
  source and golden-output fingerprints.

Use `import Cjr` to load the complete development. Definitions are in namespace
`Cjr`; sample programs are in `Cjr.Examples`. `Main.lean` demonstrates execution.

## Semantic details preserved

Immutable `let` substitutes values. Mutable `var` allocates a stack slot,
rewrites reads and assignments to slot operations, and deletes the slot when
its body returns a value. Closures can capture these slots; escaping a scope
does not prolong the slot's lifetime. Assigning an unbound name is stuck.

Raw allocation accepts strictly positive lengths, initializes every cell to
integer zero, records the block length, and advances the shared fresh counter.
Only a registered block base can be freed. Free deletes the entire block and
never rewinds the counter. Loads and stores require a present cell. Pointer
offset is unchecked integer addition; accesses can therefore be stuck later.

Structures are values; changing a structure field updates its mutable stack
binding. Objects have a separate field heap and no deallocation rule. Object
creation reserves one fresh identifier even when it has zero fields. Field
stores require an existing field; they cannot extend objects.

Evaluation is strict and left to right, including Boolean `and`. Integer
arithmetic is unbounded. Division and remainder truncate toward zero and are
stuck at divisor zero. Bit operations use infinite two's-complement semantics,
implemented from natural-number bits. Floating literals retain the upstream
integer payload; upstream defines no floating arithmetic rules. Equality is
only defined on integers. Null has no dereference rule. `while` unfolds into
`if` and sequencing. No rule produces observations or spawned threads, so
those uniformly empty upstream arguments are omitted.

## Verification scope

Lean checks the definitions, proof terms, and example equalities. The initial
state's well-formedness and freshness for all heap kinds are proved. This port
does not claim a mechanized equivalence with the Rocq source or a port of its
Iris program logic, adequacy theorem, generic libraries, the generic-source language/printer, or all
upstream well-formedness preservation lemmas. Source correspondence is pinned
and reviewable; it is not itself a cross-prover equivalence proof.

The audit reports only Lean's standard logical axioms (`propext`, and
`Quot.sound` for some heap and list proofs); no theorem depends on
`sorryAx` or an added axiom. The contextual soundness theorem is one-way: this
version does not separately prove contextual reduction complete for `step`.

## Cangjie printer

`Cjr.Cangjie` ports the monomorphic printer in upstream `cj_print.v`. It handles
literals, closures, named functions, recursive calls, argument packs and aliases,
mutable locals, control flow, pointer allocation/read/write/free, structures,
classes, methods, and self-referential fields. Layouts and signatures are supplied
explicitly because the core AST is untyped. Placeholder addresses can be restored
to parameter names using `renamePtr`, matching upstream behavior.

```sh
lake exe cjr --list
lake exe cjr --emit factorial generated.cj
lake exe cjr --emit swap swap.cj
lake exe test-printer
lake exe test-linked-list
lake exe test-iterator
lake exe test-mergesort
python3 tests/native_printer.py
```

`--emit NAME` without an output path writes source to stdout. Running `cjr`
without arguments still runs the operational-semantics demonstrations.
The printer tests emit all 14 programs into `.lake/printer-output/` by default;
an optional directory argument changes that destination. Checked-in generated
examples are under `generated/cangjie/`.

The Lean API offers two modes:

- `ex env indent expr`, `exv env indent value`, `printProg program`, and
  `printProgWith rules program` reproduce the legacy printer, including its
  `/* unsupported: ... */` markers. Eight golden files match upstream exactly
  after removing the first-line generator banner.
- `emit program` returns `Except (List String) String`. It rejects unsupported
  markers, invalid or duplicate layout/function/field names, malformed basic
  signatures, missing method owners/receivers, and duplicate sanitized parameters.
  `emit_metadata_checked` proves successful emission passed the metadata checks.
  This is a metadata/printability check, not a static type system or a verified
  semantics-preserving compiler.

Checked emission also corrects a legacy-printer mismatch: CJR's conjunction is
strict, whereas native `&&` short circuits. `emit` uses an applied two-argument
lambda to evaluate both operands before conjunction. Compatibility printing
retains upstream's `&&` output. The native strict-conjunction regression checks
that a false left operand still permits a right-operand assignment.

Native bulk-copy replacement remains opt-in through `CopyRules`, with the same
exact method-body and loop-body matching as upstream. No rewrite is enabled by
default. The caller is responsible for the validity of any supplied rewrite
policy; the Lean printer does not prove a native `memmove` refinement.

The generic-source AST and `generic_print.v` are separate from this monomorphic
operational language and are not included. Native integer bounds, caller-supplied
type strings, layout disambiguation by arity, and the legacy argument-pack
conventions retain the original printer's limitations.

### Printer validation

`sh scripts/check.sh` builds the library and all executables, runs the proof
assumption audit, compares all eight upstream golden files, and checks individual
formatting, rejection, and copy-policy cases. `tests/native_printer.py` additionally
requires Cangjie 1.0.5; set `CJC`, `CANGJIE_HOME`, or `SDKROOT` if necessary. It
compiles and executes each emitted program unchanged, then compiles a second
version replacing only `main` with native result assertions. It uses temporary
files and, on newer macOS systems, a temporary compatible copy of SDK linker
stubs; it does not edit the installed SDK.

All 17 native cases passed with Cangjie 1.0.5: arithmetic, mutable structures, raw
cell operations, pointer swap, block summation, class fields, framed calls,
function tables, factorial, methods, self-referential fields, strict conjunction,
a mutable counter, raw-memory cleanup, the verified linked-list implementation, its stateful iterator, and mergesort.

## Verified linked lists

`Cjr/LinkedList/` implements persistent heap-allocated integer lists in CJR and
proves their contracts directly against the executable small-step semantics.
It includes empty/cons, head/tail/isEmpty, length, append, and accumulator reverse.
For arbitrary finite represented lists, the proofs establish termination,
correct contents, preservation of all existing object cells, and unchanged
stack/raw/block heaps. The algebra includes append identities and associativity,
reverse involution and distribution over append, length laws, and head/tail laws.

See [the formal specification and proof guide](Cjr/LinkedList/README.md).
`Models` gives compositional contracts for actual CJR programs; the laws concern
represented sequences rather than equality of newly allocated pointers. A
finite interpreter-fuel witness, uniqueness of completed execution results, and
absence of stuck finite maximal executions are proved as well.

```sh
lake exe test-linked-list
lake exe cjr --emit linked_list linked_list.cj
```

The generated implementation is in `generated/cangjie/linked_list.cj`. Linked-list
regressions and the general proofs are included in `scripts/check.sh`; the native
Cangjie harness additionally checks its exported operations and algebraic examples.

## Linked-list iterator

`Cjr/LinkedList/Iterator/` adds an iterator retaining the original list and a
mutable cursor. `iterator(list).next()` returns a native `?ListNode`: Some of the
current node while advancing one link, or stable None at exhaustion. The list
itself is unchanged. The CJR implementation and arbitrary-list proofs establish
ordered traversal, exact cursor movement, termination, stable exhaustion, and
preservation of every field except that iterator's cursor.

See [the iterator specification](Cjr/LinkedList/Iterator/README.md).

```sh
lake exe test-iterator
lake exe cjr --emit list_iterator list_iterator.cj
```

Generated code is in `generated/cangjie/list_iterator.cj`. The printer uses explicit
`nativeOptions` metadata to lower the core's tagged option to native Some/None.
The native and CJR tests cover repeated exhaustion and independent iterators in
addition to the general Lean proofs.

## Verified mergesort

`Cjr/LinkedList/MergeSort/` implements persistent top-down mergesort using balanced
alternating split and recursive merge. The independent mathematical specification
is pairwise nondecreasing order plus `List.Perm` of the input, preserving every
integer's multiplicity. The general `sort_correct` theorem connects actual CJR
small-step execution to that specification and proves preservation of all old
heap cells. Termination and absence of stuck finite maximal executions are also
proved for arbitrary finite represented lists.

See [the mergesort specification and proof guide](Cjr/LinkedList/MergeSort/README.md).

```sh
lake exe test-mergesort
lake exe cjr --emit mergesort mergesort.cj
python3 tests/native_printer.py --only mergesort
```

The output is `generated/cangjie/mergesort.cj`. The CJR regressions exhaust 364
small inputs and include larger, negative, duplicate-heavy and boundary cases;
the native Cangjie tests additionally check the exported split, merge, sort,
and input preservation. A standard-library sorting function is used only as a
runtime test reference, not by the implementation or correctness proofs.

## Proven mergesort step budget

The complexity development counts actual CJR transitions, including allocations,
bindings, comparisons and field accesses. It proves Theta(n log2 n) for this
implementation, rather than importing the usual mergesort complexity claim.
For `n >= 1`, a safe worst-case budget is `37n(ceil(log2 n)+1)-30` reductions;
empty input takes 3. A matching-order lower bound is `15n floor(log2 n)`.
These are abstract language steps, excluding input construction, not CPU time.

See [the exact accounting and bound proofs](Cjr/LinkedList/MergeSort/COST.md).

```sh
lake exe estimate-mergesort 1000
lake exe test-mergesort-cost
```

The estimator reports a 406,970-step safe budget for 1,000 nodes. `Counted.lean`
connects the exact cost model to small-step execution; `Bounds.lean` proves the
logarithmic bounds and that the budget is sufficient interpreter fuel.

## Ranked-choice voting and its proved properties

[`voting/`](voting/README.md) implements single-winner instant-runoff voting and
sequential selection of a user-supplied number of choices. The counting loops,
transfers, allocations, residual Pareto checks and result-list construction are
CJR expressions, executed by the same small-step interpreter and emitted through
the checked Cangjie printer. The input supports partial rankings and abstentions.
Tied minimum-count candidates are eliminated by greatest candidate ID, making
the result deterministic but dependent on candidate numbering in tied elections.
Sequential selection removes each elected candidate and starts a fresh runoff;
it is not proportional STV.

The voting development separates general, kernel-checked theorems from finite
execution tests:

- **Voter anonymity:** permuting whole ballots leaves the checked generated
  program unchanged, preserving its executions, returned values and final states.
  `election_anonymous` covers single-winner elections; `topElection_anonymous`
  covers every selection limit. Their interpreter counterparts hold for every
  fuel value. The proof canonicalizes voter order without changing preference
  order or repeated ballots. This is invariance under voter permutation, rather
  than candidate neutrality or a claim about identity privacy.
  See [the anonymity proof](voting/ANONYMITY.md) and
  [the multi-choice development](voting/TOP_CHOICES.md).
- **Pareto exclusion for the checked single-winner entry point:** if every voter
  strictly prefers valid candidate A to B, no completed election returns B.
  A ranked candidate is preferred to an omitted one. The generated CJR result
  guard rejects unanimously dominated results, and `election_pareto_all_profiles`
  proves the exclusion against operational execution, including empty electorates.
  `paretoGuard_accepts` proves that an eligible result is preserved together with
  the core's final state. This is a safety theorem: it neither proves termination
  nor establishes that the unguarded counting core always passes the guard.
  See [the statement, guard and proof](voting/PARETO.md).
- **Monotonicity is false:** `election_not_monotone : ¬ Monotone` proves a concrete
  seven-voter counterexample for the checked single-winner program. Raising the
  original winner on one ballot changes the winner from candidate 0 to candidate
  1. Kernel-checked interpreter observations, interpreter soundness and execution
  determinism establish both outcomes and exclude the original winner after the
  change. All candidates are Pareto-eligible, so the guard is not responsible.
  See [the ballots and counterproof](voting/MONOTONICITY.md).

The multi-choice implementation checks Pareto eligibility against the residual
profile at each position. Its general operational Pareto theorem, distinctness
and length bounds, termination and full sequential-IRV correctness are not
claimed. Nor does the voting development prove arbitrary-input correctness or
memory safety of the counting core, or semantics preservation of native code
emission. Native functions accepting raw matrices bypass the checked Lean
builder's input validation and canonicalization. These boundaries matter when
using the extracted implementation independently.

Validation adds 413 single-winner and 1,057 multi-choice completed CJR executions
against independent reference implementations, checking temporary-memory cleanup,
plus 97 voter-swap regressions. The native harness checks 262 single-winner and
75 multi-choice profiles/limits, input preservation, guarded results, and the two
monotonicity-counterexample outcomes. These finite checks supplement the proofs;
they do not replace general theorems. The voting audits report only standard
Lean axioms, with no admitted proofs or project-defined axioms.

```sh
sh scripts/check.sh
# Native checks additionally require Cangjie 1.0.5:
(cd voting && python3 test_native.py)
```

The main check script includes the voting proof audits and CJR regressions.
For interfaces, examples and detailed assumptions, see [the voting README](voting/README.md).
