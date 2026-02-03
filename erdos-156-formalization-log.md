# Erdős Problem 156 Formalization Log

The problem asks for the existence of a maximal Sidon set in $\{1,\dots,N\}$ of size $O(N^{1/3})$.

## Problem Statement

Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?

## Formalization Details

- **Sidon set**: Uses the `IsSidon` definition from `FormalConjecturesForMathlib.Combinatorics.Basic`.
- **Maximal Sidon set**: Uses `IsMaximalSidonSetIn` from the same location, which defines a Sidon set $A \subseteq \{1, \dots, N\}$ that cannot be extended within the same interval.
- **Size $O(N^{1/3})$**: Formalized as $\exists C, \forall N, \exists A, |A| \le C N^{1/3}$. 
- **Open Status**: The problem is formalized as a conjecture using `answer(sorry)`.

## Status

Open. The greedy construction gives a lower bound of $\gg N^{1/3}$. Ruzsa [Ru98b] has constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$.

## References

- [ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
- [Ru98b] I. Z. Ruzsa, "An infinite maximal Sidon set", J. Number Theory 68 (1998), 18–26.
