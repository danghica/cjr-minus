# Monotonicity: a proved counterexample

This instant-runoff implementation does **not** satisfy monotonicity.
`election_not_monotone` in `NotMonotone.lean` proves the negation for the actual
checked CJR− entry point. The voting implementation is unchanged by this work.

## Property

If C wins, moving C upward on voters' ballots, while preserving the relative
order of all other candidates, must leave C the winner.

`BallotRaises` formalizes a strict upward move across a nonempty segment of a
ranking without duplicates. `ProfileRaises` relates profiles voter by voter:
each ballot is unchanged or raises C. `Monotone` requires preservation of a
completed winning execution, even restricting both profiles to complete strict
rankings of the registered candidates.

## Seven voters, one changed ballot

Let A = 0, B = 1, C = 2. Initially:

- Two voters rank A > B > C.
- Two voters rank B > A > C.
- Three voters rank C > B > A.

First-choice totals are A: 2, B: 2, C: 3. The specified tie rule eliminates
the greatest ID among the minimum-count candidates, so B is eliminated.
Its two ballots transfer to A, and **A wins 4–3**.

Exactly one of the last three voters now changes C > B > A to **A > C > B**.
Only A moves, from last to first. C remains above B; the other six ballots stay
unchanged.

New first-choice totals are A: 3, B: 2, C: 2. The same tie rule eliminates C.
Its two remaining ballots transfer to B, and **B wins 4–3**.

Raising winner A therefore makes A lose. Both tie decisions follow the existing
highest-ID policy. All ballots are valid and complete. Every candidate remains
Pareto-eligible on both profiles, so the Pareto guard does not cause this failure.
Both returned results are actual candidates, not the sentinel `-1`.

## Machine-checked evidence

`Monotonicity.lean` defines the property and profiles, proves their canonical
orders, and proves these exact interpreter observations:

```lean
theorem original_observed : observed original = some 0
theorem raised_observed   : observed raised = some 1
```

`observed` constructs the full checked election, including setup, canonical voter
ordering, counting, cleanup and the Pareto guard, then runs the CJR interpreter
with 20,000 fuel. These execution equalities use **`decide +kernel`**, which checks
computation inside Lean's kernel. They use no `native_decide` or external oracle.
Canonicalization is justified by the proved sorting and permutation lemmas.

`NotMonotone.lean` proves:

- `original_complete` / `raised_complete`: all ballots are complete rankings.
- `original_all_eligible` / `raised_all_eligible`: no Pareto filtering occurs.
- `raises_winner`: exactly the allowed upward move relates the profiles.
- `original_wins` / `raised_loses`: actual small-step executions return 0 and 1,
  using the existing interpreter-soundness theorem.
- `raised_cannot_win`: deterministic execution excludes any successful result of
  0 on the modified profile, independently of a particular fuel bound.
- `election_not_monotone : ¬ Monotone`: the universal property is false.

A single verified counterexample refutes the universal property. No unproved
execution-refinement premise is used. The axiom audit lists only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; there are no admitted lemmas or
project-defined axioms.

## Verification

Run `sh check.sh` after building the parent CJR library. It checks the proofs and
`AuditMonotonicity.lean`, and reruns both executions as runtime regressions. The
anonymity and Pareto checks remain in the suite.

`python3 test_native.py` additionally compiles and executes the two emitted
counterexample elections in `monotonicity_checks.cj`. These assertions are
regenerated from CJR expressions by `TestVoting.lean`.

Restoring monotonicity requires a change to the voting rule and a new proof.
A theorem asserting it for this existing program cannot be supplied truthfully.
