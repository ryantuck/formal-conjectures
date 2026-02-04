# Erdős Problem 175 Formalization Log

## Conjecture

Show that, for any $n \geq 5$, the binomial coefficient $\binom{2n}{n}$ is not squarefree.

## Formalization

I formalized the statement as `∀ (n : ℕ), n ≥ 5 → ¬Squarefree (Nat.choose (2 * n) n)`.
The problem is marked as "solved" on erdosproblems.com. It was proved by Sárközy (1985) for sufficiently large $n$, and by Granville and Ramaré (1996) for all $n \geq 5$.

## Status

The conjecture is formalized but not proven. The theorem `erdos_175` has a `sorry` placeholder.
Built successfully using `lake build FormalConjectures/ErdosProblems/175.lean`.
