# Erdős Problem 216 - Formalization Log

## Problem Statement

Let $g(k)$ be the smallest integer (if any such exists) such that any $g(k)$ points in $\mathbb{R}^2$ contains an empty convex $k$-gon (i.e. with no point in the interior). Does $g(k)$ exist? If so, estimate $g(k)$.

## Status

**DISPROVED** - This has been solved in the negative.

## Key Results

1. **$g(4) = 5$** - Erdős observed this is the same as the happy ending problem
2. **$g(5) = 10$** - Proved by Harborth [Ha78]
3. **$g(6) = 30$** - Proved by Heule and Scheucher [HeSc24]
   - Nicolás [Ni07] and Gerken [Ge08] independently first showed that $g(6)$ exists
4. **$g(k)$ does not exist for $k \geq 7$** - Proved by Horton [Ho83]

## Formalization Details

### Main Components

1. **`HasEmptyConvexNGon`**: Defines what it means for a set of points to contain an empty convex $n$-gon
   - A subset of $n$ points forms a convex $n$-gon
   - No other point from the original set lies in the interior of the convex hull

2. **`cardSet`**: The set of values $N$ such that any $N$ points in the plane (with no three on a line) contain an empty convex $k$-gon

3. **`g(k)`**: The minimum value in `cardSet k` (using `sInf`)

### Theorems Formalized

- `erdos_216`: Main theorem stating that $g(k)$ does not exist for all $k$
- `erdos_216.g4`: $g(4) = 5$
- `erdos_216.g5`: $g(5) = 10$ (Harborth)
- `erdos_216.g6_exists`: $g(6)$ exists (Nicolás, Gerken)
- `erdos_216.g6`: $g(6) = 30$ (Heule and Scheucher)
- `erdos_216.not_exists_ge_7`: $g(k)$ does not exist for $k \geq 7$ (Horton)

## Relationship to Other Problems

This is a variant of the "happy ending problem" (Erdős Problem 107), which asks for the same question without the "no point in the interior" restriction. Problem 107 is still open, while Problem 216 has been completely resolved.

## References

- [Ha78] Harborth, H., _Konvexe Fünfecke in ebenen Punktmengen_. Elem. Math. (1978), 116-118.
- [Ni07] Nicolás, C. M., _The empty hexagon theorem_. Discrete Comput. Geom. (2007), 389-397.
- [Ge08] Gerken, T., _Empty convex hexagons in planar point sets_. Discrete Comput. Geom. (2008), 239-272.
- [Ho83] Horton, J. D., _Sets with no empty convex 7-gons_. Canad. Math. Bull. (1983), 482-484.
- [HeSc24] Heule, M. J. and Scheucher, M., _The empty hexagon number is 30_. arXiv preprint arXiv:2404.16223 (2024).

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/216.lean`
