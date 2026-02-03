# Erdős Problem 159 Formalization Log

The problem asks whether the Ramsey number $R(C_4, K_n)$ is $O(n^{2-c})$ for some constant $c > 0$.

## Problem Statement

There exists some constant $c>0$ such that
$$R(C_4,K_n) \ll n^{2-c}.$$

## Formalization Details

- **Ramsey number $R(C_4, K_n)$**: Formalized as `erdos_159_Ramsey n`, the smallest $N$ such that every graph on $N$ vertices contains a $C_4$ as a subgraph or an independent set of size $n$.
- **Subgraphs**: Used the `⊑` notation (`SimpleGraph.IsContained`) for $C_4 \subseteq G$.
- **$C_4$**: Represented by `cycleGraph 4`.
- **Independence number**: Used the `α(G)` notation (`SimpleGraph.indepNum`) for the size of the largest independent set.
- **Asymptotic bound**: The Vinogradov notation $\ll$ is formalized using `Asymptotics.isBigO` (notation `=O[atTop]`).
- **Conjecture**: Formalized as $\exists c > 0, R(C_4, K_n) = O(n^{2-c})$.

## Status

Open. The current known upper bound is $O(n^2 / (\log n)^2)$.

## References

- [erdosproblems.com/159](https://www.erdosproblems.com/159)
- [Sp77] J. Spencer, "Asymptotic lower bounds for Ramsey functions", Discrete Math. 20 (1977), 69–76.
