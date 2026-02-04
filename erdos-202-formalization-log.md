# Erdős Problem 202 Formalization Log

## Problem Statement

Let $n_1 < \dots < n_r \leq N$ with associated $a_i \pmod{n_i}$ such that the congruence classes are disjoint (that is, every integer is $\equiv a_i \pmod{n_i}$ for at most one $1 \leq i \leq r$). How large can $r$ be in terms of $N$?

## Discovery and Analysis

- The problem asks for the maximum size $f(N)$ of a set of disjoint congruence classes with distinct moduli up to $N$.
- Disjointness of $a_i \pmod{n_i}$ and $a_j \pmod{n_j}$ is equivalent to $\gcd(n_i, n_j) 
mid (a_i - a_j)$.
- Erdős and Szemerédi (1968) proved $f(N) = o(N)$ and gave initial bounds.
- de la Bretèche, Ford, and Vandehey (2013) improved the bounds to:
  $$ \frac{N}{L(N)^{1+o(1)}} < f(N) < \frac{N}{L(N)^{\sqrt{3}/2+o(1)}} $$
  where $L(N) = \exp(\sqrt{\log N \log \log N})$.
- They conjecture that the lower bound is the truth.

## Formalization Plan

- Define $f(N)$ as the `sSup` of `r` such that there exist distinct moduli $n_i \le N$ and residues $a_i$ with disjoint congruence classes.
- Represent congruence classes as sets: `{a_i} + Ideal.span {n_i}`.
- State the conjecture as an asymptotic bound using $\epsilon$ and $N_0$.

## Lean Implementation Details

- Used `Pairwise` for the disjointness condition on `Fin r`.
- Used `Real.exp`, `Real.sqrt`, `Real.log` for the bound.
- Included the reference [BFV13].

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/202.lean`.
