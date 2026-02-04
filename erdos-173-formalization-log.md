# Erdős Problem 173 Formalization Log

## Conjecture

In any $2$-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$, there is a monochromatic congruent copy of $T$.

## Formalization

I defined `IsCongruent` for sets of points in `EuclideanSpace ℝ (Fin 2)` using isometries.
The theorem `erdos_173` states that for any 2-colouring `f`, there exists at most one triangle $T_0$ such that for any other triangle $T$, there is a congruent copy $T'$ that is monochromatic under `f`.

Note: I represented a triangle as a set of 3 points. The "at most one triangle" is interpreted as "all congruent copies of a single triangle $T_0$".

## Status

The conjecture is formalized but not proven. The theorem `erdos_173` has a `sorry` placeholder.
This is a problem in Ramsey theory/geometric Ramsey theory.
In some colourings, a single equilateral triangle must be excluded.
Shader (1976) proved it for right-angled triangles.
