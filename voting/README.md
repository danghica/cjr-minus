# Ranked-choice voting in CJR−

**Sequential ranked-choice voting**, using an instant-runoff election for each
position and a user-supplied selection limit, built on the CJR operational semantics and
checked Cangjie printer from the enclosing `danghica/cjr-minus` project.
The voting algorithm itself is a `Cjr.Expr`: every count, transfer, allocation,
and loop executes through CJR's small-step interpreter. Lean builds and validates
the input; it does not calculate the implementation's winner.

## Rules

- Candidate IDs are `0` through `n-1`. Each ballot is an ordered, possibly partial
  ranking. Empty rankings are allowed; duplicate and unknown IDs are rejected.
- Each round counts the first still-active candidate on each ballot.
- A candidate wins with strictly more than half of the non-exhausted ballots.
  Exactly half does not suffice.
- Otherwise eliminate exactly one candidate with the fewest votes, including
  candidates with zero votes. If tied, eliminate the **greatest candidate ID**.
  This is an explicit deterministic policy; ID assignment can affect tied results.
- Recount after elimination, transferring ballots to their next active choice.
- Return `-1` if there are no candidates or no remaining non-exhausted ballots.
  A sole remaining candidate wins only if at least one ballot supports them.
- The checked entry point also returns `-1` if its final Pareto guard rejects the
  core's result. See the proof scope below.

For multiple choices, elect one winner, remove that ID from every ballot, and
repeat with fresh elimination rounds until the requested count is reached or
remaining ballots are exhausted. Results are ordered and may contain fewer
choices than requested. This is sequential IRV, not proportional STV.
See [the multi-choice API, behavior and proof scope](TOP_CHOICES.md).

## Files and use

- `TopChoices.lean` and `TestTopChoices.lean`: multi-choice CJR implementation,
  runtime residual Pareto guard, generalized anonymity proof, and 1,057 oracle
  regressions across selection limits.
- `Voting.lean`: CJR algorithm (`body`, `votingFn`), validated election builder
  (`election`), and native export metadata (`program`).
- `Canonical.lean` and `Anonymity.lean`: canonical voter ordering and the proved
  anonymity theorem for the checked entry point. See [the theorem and proof](ANONYMITY.md).
- `ReturnSafety.lean`, `ParetoGuard.lean`, and `Pareto.lean`: CJR return-value
  safety, the Pareto guard, and its execution-level exclusion theorem. See
  [the Pareto theorem and proof](PARETO.md).
- `Monotonicity.lean` and `NotMonotone.lean`: the monotonicity property and a
  kernel-checked seven-voter counterexample. See [the countertheorem](MONOTONICITY.md).
- `TestVoting.lean`: interpreter regressions, independent functional oracle,
  malformed-input tests, memory cleanup checks, and checked code generation.
- `ranked_choice.cj`: generated Cangjie implementation and sample invocation.
- `test_native.py`: native result and input-preservation checks; uses the parent
  project's Cangjie 1.0.5 compiler setup.
- `pareto_checks.cj`: generated native tests for the guarded election and five
  injected core results, regenerated alongside the sample.
- `monotonicity_checks.cj`: generated native checks of the two counterexample
  elections, verifying that raising winner 0 produces winner 1.

After building the parent project with Lean 4.24.0 (`lake build`), run here:

```sh
sh check.sh
python3 test_native.py
```

If Lean is not on your path, pass `LEAN=/absolute/path/to/lean sh check.sh`.
The first command regenerates `ranked_choice.cj`, including both single- and
multi-choice functions, from checked CJR expressions.
The native test requires Cangjie 1.0.5; `CJC` can select its compiler.

In Lean, for example:

```lean
import TopChoices
open Cjr Cjr.Voting
-- 0 leads initially, but elimination of 2 transfers two ballots to 1.
#eval do
  let e ← election 3 [[0], [0], [0], [1], [1], [2, 1], [2, 1]]
  pure (run 1000000 e stateInit)
-- done with integer 1, and no remaining allocated memory.
```

For an ordered list of up to two choices:

```lean
#eval do
  let e ← topElection 3 2 [[0], [0], [0], [1], [1], [2, 1], [2, 1]]
  pure (run 2000000 e stateInit)
-- An owned ListNode chain containing [1, 0].
```

## Native interface

```cangjie
func rankedChoice(n: Int64, m: Int64, width: Int64,
                  ballots: CPointer<Int64>): Int64
func rankedChoices(n: Int64, m: Int64, width: Int64,
                   ballots: CPointer<Int64>, limit: Int64): ListNode
```

`ballots` is a read-only row-major `m × width` matrix, with rankings padded by
`-1`. The caller owns that memory. The function allocates and frees its own active
flags and counts; it leaves the matrix untouched. `election` constructs and frees
the matrix as well, allocating one unused cell when the matrix is empty because
CJR forbids zero-length allocation.

Direct native callers must supply nonnegative dimensions and enough readable
memory, with distinct in-range IDs followed by padding in each row. The checked
Lean builder enforces the ranking requirements. The low-level function ignores
out-of-range entries defensively, but does not reject duplicate IDs or malformed
padding. Dimensions, products, doubled vote counts and allocation sizes must fit
native integer/address bounds, and native allocations must succeed. CJR integers
are unbounded; its allocator does not model allocation failure.

The checked `election` builder puts whole ballots in canonical voter order before
constructing the matrix. Rankings and repeated ballots are preserved. This makes
every permutation of the voter list generate the exact same CJR program, with a
Lean-checked execution-level anonymity proof. Direct native calls bypass this
preparation and are outside that theorem.

The checked builder also adds a CJR guard which accepts only a candidate who is
not unanimously dominated; otherwise it returns `-1`. This gives a Lean-checked
Pareto exclusion theorem. A ranked candidate is preferred to an omitted one;
omitting both expresses no strict preference. Direct native calls bypass the
guard. The theorem does not establish that the unguarded counting core satisfies
Pareto, or that the guard's fallback is unreachable on valid inputs.

At most `n` rounds run: each nonterminal round removes one active candidate.
The algorithm uses `O(n)` scratch cells and `O(n * (m * width + n))` worst-case
work, excluding input construction. These are algorithmic bounds, not a proved
CJR transition-cost theorem.
Canonical input preparation additionally sorts `m` ballots, using `O(m log m)`
ballot comparisons, each taking up to `O(width)` work.
Pareto eligibility preparation checks every candidate pair against the ballots;
the emitted result guard compares at most `n` IDs and allocates no memory.

Validation covers 413 completed CJR executions (all ordered profiles of up to
two ballots over all 16 partial rankings of three candidates, plus targeted and
larger profiles), with an independent oracle and cleanup checks. Native checks
also verify that ballot cells remain unchanged. This implementation does not
include an arbitrary-input Lean correctness or memory-safety proof.
The anonymity and Pareto theorems are separate general properties of the updated
checked entry point; they do not require that correctness proof for the core.
