# Selecting a user-supplied number of choices

`topElection candidateCount limit ballots` constructs a CJR− program returning
an owned `ListNode` chain of up to `limit` distinct candidate IDs, in election
order. `limit` may be zero; the checked builder rejects a limit greater than the
candidate count.

For each position the program runs the existing instant-runoff algorithm on the
remaining rankings, checks the result against unanimous domination in that
residual profile, appends the winner, and removes that ID from every ballot.
It starts a fresh IRV election for the next position. It stops at the requested
limit, exhaustion of all remaining ballots, or rejection by the result guard.
Eliminated candidates from a previous position are eligible again for the next
position unless they were elected. Votes are not proportionally reweighted;
this is sequential IRV, not proportional STV or a list of final-round survivors.

The input matrix is read-only. `rankedChoicesInto` makes one scratch copy and
writes into a caller-owned output buffer, returning the count written.
`rankedChoices` supplies that buffer, converts it to a linked list in selection
order and frees all temporary raw memory. Result objects remain owned by the
caller (and are managed by the Cangjie runtime after extraction).

## Native API

```cangjie
func rankedChoices(n: Int64, m: Int64, width: Int64,
                  ballots: CPointer<Int64>, limit: Int64): ListNode
func rankedChoicesInto(n: Int64, m: Int64, width: Int64,
                      ballots: CPointer<Int64>, limit: Int64,
                      output: CPointer<Int64>): Int64
```

The existing `rankedChoice` single-result API remains available. All three
functions are emitted from CJR expressions, as is the new runtime Pareto test.
Direct callers must supply valid dimensions, nonnegative limits, sufficient
memory and valid padded rankings, and respect native integer/allocation limits.
The checked builder bounds the limit by the candidate count. Native callers
are responsible for satisfying those preconditions; the functions leave inputs intact.

## Proofs and limits

`topElection_program_anonymous` proves exact generated-program equality under
any voter permutation for every limit. `topElection_anonymous` lifts this to
unbounded CJR execution; `topElection_run_anonymous` covers every fuel value.
The proofs are kernel-checked, without admitted lemmas or added axioms.

The existing single-choice anonymity and Pareto theorems and the proved
monotonicity counterexample are rerun unchanged. Their statements still concern
the single-choice `election` API. In particular, excluding a candidate dominated
in the original profile from *every* output position would be wrong: after its
dominator has already been elected, that candidate can be a legitimate next
choice. The new runtime guard uses the residual profile at each position.
The general operational proof of that dynamic guard, distinctness/length bounds,
termination and full sequential-IRV correctness are not claimed here. Those
multi-choice properties are exercised by the independent-oracle regressions.

`TestTopChoices.lean` checks 1,057 CJR executions: all ordered pairs of the 16
partial three-candidate rankings, for limits 0–3, plus empty, repeated, exhausted
and multi-voter cases. It checks ordered results against an independent
sequential reference and verifies temporary raw-memory cleanup. Native tests
check 75 multi-choice profiles/limits and verify input preservation. Tests also
cover excessive limits and invalid rankings.

## Verification

After building the parent library, run `sh check.sh` and `python3 test_native.py`
from this directory. The Lean checks regenerate the Cangjie implementation and
native guard/counterexample fixtures. See [the voting guide](README.md) for the
compiler version, API examples, and proof boundaries.
