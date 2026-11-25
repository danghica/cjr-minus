# How many CJR steps does mergesort take?

The implemented sort has worst-case growth **Theta(n log2 n)**. A verified safe
budget for sorting an already represented list is:

- `n = 0`: exactly **3** CJR transitions.
- `n >= 1`: at most **37 n (ceil(log2 n) + 1) - 30** CJR transitions.

For example, a list of 1,000 nodes takes at most **406,970** transitions; a list of
1,000,000 nodes takes at most **776,999,970**. These are safe upper bounds, not
claims of exact worst-case attainment or measurements of CPU time.

For every valid input with `n >= 1`, the count is also at least
**15 n floor(log2 n)**. Thus the lower and upper bounds have the same asymptotic
order. For `n >= 2`, the formal constant-factor statement is:

```
15 n floor(log2 n) <= actual steps <= 111 n floor(log2 n)
```

The tighter size-only budget above is preferable for estimating a concrete `n`.
The factor 111 is a deliberately simple witness for the Theta statement.

## What one step means

`Cjr/CountedExecution.lean` defines `StepsN n e s e' t`: exactly `n` applications
of the existing executable CJR `Step` relation. A context-lifted reduction still
counts once. The cost includes application, immutable binding, branching, field
access, arithmetic/comparison, structure assembly, and allocation reductions.
Returning a value takes no additional transition.

This is the language's abstract reduction count. Heap lookup, substitution,
context decomposition and unbounded integer primitives are performed within a
transition; their Lean implementation costs and integer bit complexity are not
charged separately. No assertion about the runtime of the association-list heap
implementation, native CPU instructions, elapsed time, or Cangjie allocation
performance follows from this model.

The input list is already present in the initial heap. Building it with `ofList`
and printing or consuming the result are outside this sorting-only budget.

## Exact accounting before approximation

`CostModel.lean` defines a pure reference `sorted`, an exact value-dependent
`sortSteps`, and helper counts. `Counted.lean` proves those counts by constructing
counted derivations for the real CJR programs, retaining the same heap
representation and preservation contracts as the correctness proof.

The exact recurrence is:

```
Split(0)   = 6
Split(n+1) = Split(n) + 15
Split(n)   = 15n + 6

Merge([], ys)                 = 7
Merge(nonempty xs, [])        = 9
Merge(x::xs, y::ys)           = 22 + cost of the selected recursive merge

Sort([])                     = 3
Sort([x])                    = 7
Sort(xs), n >= 2             = Sort(a) + Sort(b)
                                + Merge(sorted(a), sorted(b)) + 15n + 21
```

In the split line, the closed form is `Split(n) = 15n + 6`.
`a` and `b` are the alternating halves, of sizes `ceil(n/2)` and `floor(n/2)`.
Each merge comparison removes one head; the merge count is bounded by
`22 (length(a) + length(b)) + 9`. Therefore:

```
Sort(xs) <= Sort(a) + Sort(b) + 37n + 30
```

The two-element counts illustrate both data dependence and the conservative
nature of the budget: `[1,2]` takes exactly 94 transitions, `[2,1]` takes exactly
96, while the size-only budget for `n=2` is 118. The difference comes from which
empty-list branch finishes merge.

## The proved logarithmic bound

`Bounds.lean` proves a tree-height theorem: for every nonempty input with
`n <= 2^k`,

```
Sort(xs) + 30 <= 37n(k+1)
```

The proof inducts on `k`. Balanced splitting gives two positive halves no larger
than `2^(k-1)`. If `F(xs) = Sort(xs) + 30`, the recurrence becomes
`F(xs) <= F(a) + F(b) + 37n`, and `F([x]) = 37`. Each level's input lengths sum
to `n`. Taking the least valid height `k = ceil(log2 n)` gives the budget.
`ceilLog_le_iff` proves that the computable `ceilLog` really is this least height.

The lower-bound proof shows that, whenever `2^k <= n`, splitting alone forces
at least `15nk` steps. Both balanced halves remain large enough to continue for
`k` levels. Taking `k = floor(log2 n)` gives the lower bound, even for already
sorted inputs. This implementation does not have a shortcut for sorted runs.

The main theorem names are:

- `split_counted`, `merge_counted`, `sort_counted`: exact transition-count bridges
  to the executable small-step semantics.
- `sortSteps_bounds`: the floor-log lower bound and ceiling-log safe budget.
- `operational_bound`: a terminating, correctly represented CJR execution with
  those bounds and preservation of the caller's heap.
- `every_execution_bound`: every completed execution has exactly the modeled
  count, using determinism of the existing semantics.
- `theta_n_log2` and `execution_theta`: explicit constant-factor Theta bounds for
  the model and for actual counted executions.
- `budget_suffices`: the size-only budget is sufficient fuel for the existing
  `run` interpreter, with a correctly represented sorted result.

All proofs are checked by Lean, without admissions or project-defined axioms.
The count is not merely an assumed recurrence or a fit to benchmark data.

## Estimate and reproduce

```sh
lake exe estimate-mergesort 1000
lake exe test-mergesort-cost
sh scripts/check.sh
```

`estimate-mergesort` accepts any nonnegative integer size and reports the safe
upper budget, the proved lower bound, the ceiling logarithm, and the cost unit.

`TestMergeSortCost.lean` independently increments a counter once for each actual
successful call to `step`. It checks the exact model and bounds on all 364 inputs
of length zero through five over `[-1,0,1]`, plus larger cases. It also checks
split's exact formula, branch-dependent two-element counts, the million-node
budget calculation, and logarithm boundaries around powers of two. The general
proofs, rather than these finite regressions, establish the bound for all sizes.
