# Erdos Problem 118 Formalization Log

## Problem Description

Erdos Problem 118 (Erdos and Hajnal) asks if $\alpha \to (\alpha, 3)^2$ implies $\alpha \to (\alpha, n)^2$ for every finite $n \ge 3$, where $\alpha$ is a cardinal, ordinal, or order type.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/118.lean`
- **Theorem Name:** `Erdos118.erdos_118`
- **Status:** Disproved.

We defined:
- `Coloring`
- `IsHomogeneous`
- `Arrow` (using `RelEmbedding` for "set of type $\beta$").

The theorem states that the implication is false, based on counterexamples like $\alpha = \omega^{\omega^2}$ and $n=5$.

## References

- [Sc99] Schipperus, R., "The partition calculus for countable ordinals", PhD thesis (1999).
- [Da99] Darby, C., "Ph.D. Thesis", University of Colorado (1999).
- [La00] Larson, J., "A counterexample in the partition calculus for countable ordinals", Math. Logic Quart. (2000).

