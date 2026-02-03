# Erdos Problem 130 Formalization Log

## Problem Description

Erdos Problem 130 (Andrásfai and Erdős) asks if the distance graph of an infinite set $A \subseteq \mathbb{R}^2$ with no three points collinear and no four concyclic can have infinite chromatic number.
The distance graph connects points at integer distances.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/130.lean`
- **Theorem Name:** `Erdos130.erdos_130`
- **Status:** Open.

We defined:
- `NoThreeCollinear`
- `NoFourConcyclic`
- `DistanceGraph`

The theorem asks for the existence of such a set $A$ with infinite chromatic number.

## References

- [Er97b] Erdős, P., "Some of my favourite problems on cycles and colourings", Paul Erdős and his Mathematics (1997).
- [AnEr45] Anning, N. H. and Erdős, P., "Integral distances", Bull. Amer. Math. Soc. (1945), 598-600.
