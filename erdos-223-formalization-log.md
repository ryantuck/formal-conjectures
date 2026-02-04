# Erdős Problem 223 - Formalization Log

## Problem Statement

Let $d\geq 2$ and $n\geq 2$. Let $f_d(n)$ be maximal such that there exists some set of $n$ points $A\subseteq \mathbb{R}^d$, with diameter $1$, in which the distance 1 occurs between $f_d(n)$ many pairs of points in $A$. Estimate $f_d(n)$.

## Status

**SOLVED**

This was originally a conjecture of Vázsonyi mentioned in Erdős [Er46b].

## Key Results

1. **$f_2(n) = n$** - Hopf and Pannwitz [HoPa34]
2. **$f_3(n) = 2n-2$** - Grünbaum [Gr56], Heppes [He56], and Strasziewicz [St57] (independently)
3. **For $d \geq 4$**: $f_d(n) = (\frac{p-1}{2p} + o(1))n^2$ where $p = \lfloor d/2 \rfloor$ - Erdős [Er60b]
4. **Exact formula** - Swanepoel [Sw09] gave an exact description of $f_d(n)$ for all $d \geq 4$ and all $n$ sufficiently large depending on $d$, including the extremal configurations

## Formalization Details

### Main Components

1. **`diameter`**: Computes the diameter of a finite set of points (the maximum distance between any two points)

2. **`countUnitDistances`**: Counts the number of unordered pairs of points with distance exactly 1

3. **`f d n`**: The maximum number of unit distances achievable in a set of $n$ points in $\mathbb{R}^d$ with diameter $\leq 1$

### Theorems Formalized

- `erdos_223.f2`: $f_2(n) = n$ for $n \geq 3$ (Hopf and Pannwitz)
- `erdos_223.f3`: $f_3(n) = 2n-2$ for $n \geq 4$ (Grünbaum, Heppes, Strasziewicz)
- `erdos_223.fd`: Asymptotic formula for $d \geq 4$ (Erdős)

## Technical Notes

- All main definitions are marked `noncomputable` as they involve real number computations
- The diameter uses bounded supremum over all pairs of points
- Unit distance pairs are counted by filtering the off-diagonal pairs

## References

- [Er46b] Erdős, P.
- [HoPa34] Hopf, H. and Pannwitz, E., _Aufgabe Nr. 167_. Jahresbericht Deutsch. Math.-Verein. (1934), 114.
- [Gr56] Grünbaum, B., _A proof of Vázsonyi's conjecture_. Bull. Res. Council Israel. Sect. A (1956), 77-78.
- [He56] Heppes, A., _Beweis einer Vermutung von A. Vázsonyi_. Acta Math. Acad. Sci. Hungar. (1956), 463-466.
- [St57] Strasziewicz, S., _Sur un problème géométrique de P. Erdős_. Bull. Acad. Polon. Sci. Cl. III (1957), 39-40.
- [Er60b] Erdős, P., _On sets of distances of $n$ points in Euclidean space_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1960), 165-169.
- [Sw09] Swanepoel

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/223.lean`
