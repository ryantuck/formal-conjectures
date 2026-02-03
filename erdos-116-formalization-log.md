# Erdos Problem 116 Formalization Log

## Problem Description

Erdos Problem 116 (conjectured by Erdős, Herzog, and Piranian [EHP58]) asks about the 2D Lebesgue measure of the level set $\{z \in \mathbb{C} : |p(z)| < 1\}$ for a monic polynomial $p$ of degree $n$ whose roots all lie in the unit disk.

The conjecture asks if this measure is at least $n^{-O(1)}$ or even $(\log n)^{-O(1)}$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/116.lean`
- **Theorem Name:** `Erdos116.erdos_116`
- **Strong Version:** `Erdos116.strong` (based on [KLR25])
- **Wagner's Upper Bound:** `Erdos116.wagner` (based on [Wa88])

The measure is represented using `MeasureTheory.volume` on `ℂ`. The polynomial is represented using `Polynomial ℂ`.

## Status

- Proved in the affirmative.
- Pommerenke [Po61] proved a lower bound of $\gg n^{-4}$.
- Krishnapur, Lundberg, and Ramachandran [KLR25] proved a lower bound of $\gg (\log n)^{-1}$.

## References

- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., "Metric properties of polynomials", J. Analyse Math. (1958), 125-148.
- [Po61] Pommerenke, Ch., "On metric properties of complex polynomials", Michigan Math. J. (1961), 97-115.
- [Wa88] Wagner, G., "On the measure of the level sets of harmonic polynomials", Monatsh. Math. (1988), 69-81.
- [KLR25] Krishnapur, M., Lundberg, E., and Ramachandran, K., "The Erdős-Herzog-Piranian conjecture on the measure of polynomial level sets", arXiv:2501.03234 (2025).
