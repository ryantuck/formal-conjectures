# Erdos Problem 117 Formalization Log

## Problem Description

Erdos Problem 117 asks for an estimate of $h(n)$, the minimal number such that any group $G$ where every subset of size $>n$ contains a commuting pair (i.e., the maximum size of a pairwise non-commuting set is $\le n$) can be covered by at most $h(n)$ Abelian subgroups.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/117.lean`
- **Theorem Name:** `Erdos117.erdos_117`
- **Status:** Proved (Pyber's bounds).

We defined:
- `IsPairwiseNonCommuting`
- `MaxNonCommutingSize`
- `CoveredByAbelianSubgroups`

The theorem states the existence of constants $c_1, c_2 > 1$ and a function $h(n)$ bounded by $c_1^n < h(n) < c_2^n$ that satisfies the covering property for all groups.

## References

- [Py87] Pyber, L., "On the number of abelian subgroups of a finite group", Period. Math. Hungar. (1987), 69-82.
- [Er90] Erdős, P., "Some of my favorite unsolved problems", A tribute to Paul Erdős (1990), 467-478.
