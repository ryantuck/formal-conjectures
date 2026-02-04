# Erdős Problem 174 Formalization Log

## Conjecture

A finite set $A \subset \mathbb{R}^n$ is called Ramsey if, for any $k \geq 1$, there exists some $d = d(A, k)$ such that in any $k$-colouring of $\mathbb{R}^d$ there exists a monochromatic copy of $A$. Characterise the Ramsey sets in $\mathbb{R}^n$.

## Formalization

I defined `IsRamsey` for finite sets in `EuclideanSpace ℝ (Fin n)`.
A "copy" of a set $A \subset \mathbb{R}^n$ in $\mathbb{R}^d$ is defined as the image of $A$ under an isometric embedding.
The problem is to find a property $P$ such that $A$ is Ramsey iff $P(A)$.
I also included the known result that Ramsey sets must be spherical.

## Status

The conjecture is formalized but not proven. The theorem `erdos_174` (characterization) and `erdos_174.spherical` (necessary condition) have `sorry` placeholders.
Erdős et al. (1973) proved that every Ramsey set is spherical.
Graham conjectured that every spherical set is Ramsey.
Leader, Russell, and Walters (2012) conjectured that a set is Ramsey iff it is subtransitive.
