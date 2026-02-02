# Erdős Problems 45-73 Formalization Session Log

## Date: February 2, 2026

## Objective
Formalize 20 unformalized Erdős problems starting after Problem 45, based on `erdos-problems-data.yaml`.

## Problems Formalized

1. **#45**: Ramsey property for unit fractions in divisors. (Verified build)
2. **#46**: Monochromatic solution to $1=\sum \frac{1}{n_i}$ in finite colorings of integers.
3. **#47**: Density threshold for monochromatic subset sums of unit fractions equaling 1.
4. **#49**: Size of subsets with increasing Euler totient values.
5. **#50**: Singularity of the distribution function of $\phi(n)/n$.
6. **#52**: Sum-product conjecture for finite sets of integers.
7. **#53**: Growth of integers formed by sums or products of distinct elements.
8. **#54**: Ramsey 2-complete sets of integers and their growth rate.
9. **#55**: Ramsey $r$-complete sets of integers for $r > 2$.
10. **#57**: Divergence of reciprocals of odd cycle lengths in graphs with infinite chromatic number.
11. **#58**: Relation between number of odd cycle lengths and chromatic number.
12. **#59**: Number of $G$-free graphs on $n$ vertices.
13. **#60**: Number of $C_4$ copies in graphs exceeding the Turan number of edges.
14. **#62**: Shared subgraphs of graphs with chromatic number $\aleph_1$.
15. **#63**: Cycles of length $2^n$ in graphs with infinite chromatic number.
16. **#65**: Sum of reciprocals of cycle lengths in graphs with $kn$ edges.
17. **#70**: Ramsey property $\mathfrak{c} \to (\beta, n)^3$ for ordinals.
18. **#71**: Cycles in infinite arithmetic progressions for graphs with large average degree.
19. **#72**: Cycle lengths in a set of density 0 for graphs with large average degree.
20. **#73**: Independent set size and bipartite subgraphs.

## Technical Details
- All formalizations use `mathlib4` conventions.
- Graph problems utilize `SimpleGraph`, `Walk`, `IsCycle`, `IsIndepSet`, and `chromaticNumber`.
- Number theory problems utilize `Nat.totient`, `Nat.primeCounting`, and `Set.HasDensity`.
- Ordinal Ramsey theory generalization was implemented for Problem 70.
- All files build successfully using `lake build`.

## Files Created/Updated
- `FormalConjectures/ErdosProblems/46.lean`
- `FormalConjectures/ErdosProblems/47.lean`
- `FormalConjectures/ErdosProblems/49.lean`
- `FormalConjectures/ErdosProblems/50.lean`
- `FormalConjectures/ErdosProblems/52.lean`
- `FormalConjectures/ErdosProblems/53.lean`
- `FormalConjectures/ErdosProblems/54.lean`
- `FormalConjectures/ErdosProblems/55.lean`
- `FormalConjectures/ErdosProblems/57.lean`
- `FormalConjectures/ErdosProblems/58.lean`
- `FormalConjectures/ErdosProblems/59.lean`
- `FormalConjectures/ErdosProblems/60.lean`
- `FormalConjectures/ErdosProblems/62.lean`
- `FormalConjectures/ErdosProblems/63.lean`
- `FormalConjectures/ErdosProblems/65.lean`
- `FormalConjectures/ErdosProblems/70.lean`
- `FormalConjectures/ErdosProblems/71.lean`
- `FormalConjectures/ErdosProblems/72.lean`
- `FormalConjectures/ErdosProblems/73.lean`
- `erdos-45-73-formalization-log.md`
