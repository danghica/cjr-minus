# Equal treatment of voters: anonymity

## Theorem

Let `B` be a finite list of ranked ballots, and let `B'` be obtained by swapping
any two voters' ballots. For every candidate count `n`, initial CJR state `s`,
returned value `v`, and final state `t`,

> The CJR program constructed by `election n B` evaluates from `s` to `(v,t)`
> if and only if the program constructed by `election n B'` does.

This is `Cjr.Voting.election_swap_anonymous` in `Anonymity.lean`. Formally, write
the voters before the first swapped ballot as `before`, the voters between the
two ballots as `middle`, and the voters after the second as `suffix`. The theorem
is:

```lean
theorem election_swap_anonymous (n : Nat)
    (before middle suffix : List (List Nat)) (a b : List Nat)
    (s : State) (winner : Val) (t : State) :
    ElectionResult n (before ++ (a :: (middle ++ (b :: suffix)))) s winner t ↔
      ElectionResult n (before ++ (b :: (middle ++ (a :: suffix)))) s winner t
```

`ElectionResult` means that `election` successfully constructs a CJR expression
and that expression evaluates using the existing `Cjr.Evaluates` small-step
semantics. It is not defined using an assumed voting specification.

More generally, `election_anonymous` proves this for **every permutation** of
voters. `election_winners_equal` proves that any two completed executions from
the same initial state return equal values and equal final states.

## Implementation change and proof

The checked `election` entry point now lexicographically sorts **whole ballots**
before constructing the input matrix. It never sorts the preferences within a
ballot. Repeated ballots retain their multiplicity. The CJR counting algorithm
(`body` / `votingFn`) is unchanged.

The checked entry point also contains the [Pareto return-value guard](PARETO.md).
Its eligible-candidate list is computed from the same canonical ballots, so the
program-equality and anonymity proofs continue to cover the complete program,
including that guard.

The proof is by construction:

1. `canonicalBallots_perm`: sorting the voter list preserves its permutation
   class, including every ballot and its multiplicity.
2. `canonicalBallots_eq_of_perm`: sorted permutations are equal. Lexicographic
   order on lists of natural numbers is total, transitive and antisymmetric,
   so a permutation class has a unique sorted sequence.
3. `election_program_anonymous`: equal canonical sequences produce exactly
   equal CJR expressions, including matrix construction and cleanup. This also
   proves that malformed-profile rejection is invariant under voter permutation.
4. `election_anonymous`: substitute those equal expressions in the operational
   execution relation. No refinement theorem about a separate voting model is
   assumed. `election_winners_equal` additionally uses CJR's proved deterministic
   execution theorem.
5. `swap_ballots_perm`: exchanging two ballots with any list of voters between
   them is a permutation; specialize step 4 to obtain the requested theorem.

`election_run_anonymous` also proves equality of `run fuel` for **every** natural
fuel value, from every initial state. Both successful and incomplete observations
are identical; the theorem does not assume some fixed test fuel is sufficient.

## Scope

This is a kernel-checked anonymity theorem for the **updated checked entry
point**, including the actual generated CJR program. Canonicalization is Lean
input preparation, before CJR execution. It is not an operational proof that the
original unnormalized `body` is invariant under permutations of raw matrix rows.
Direct native callers of `rankedChoice` bypass this normalization and are outside
this theorem. The general termination and functional correctness of the
counting core, and correctness of the Cangjie printer, are also separate claims.

The theorem imposes no bound on voter count, ballot length, or candidate count.
It needs no distinct-voter-ballot assumption and covers empty and repeated
ballots. In particular it applies to every valid input profile. It establishes
voter anonymity, not candidate neutrality: the highest-ID elimination tie rule
still distinguishes candidates.

The counting rule is consistent with this normalization: for any active candidate
set, a ballot's first active preference depends only on that ballot. Permuting
ballots permutes those choices, preserving their count for every candidate and
the number of non-exhausted ballots. Consequently the majority decision and
ID-based elimination decision in every round are unchanged. The mechanized
execution-level proof above uses canonicalization rather than relying on this
algorithmic argument as an unproved execution-refinement premise.

## Verification

Run `sh check.sh` after building the parent CJR library. It checks the theorem
files, prints their axiom dependencies, reruns the interpreter regressions, and
regenerates the Cangjie sample. `python3 test_native.py` checks native execution.

The audit reports only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. There are no `sorry` placeholders, project-defined axioms, or
`native_decide` proofs. The finite voter-swap regressions supplement the
unbounded theorem; they are not the proof of anonymity.
