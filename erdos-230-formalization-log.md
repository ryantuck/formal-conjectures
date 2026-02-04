# Erdős Problem 230 - Formalization Log

## Problem Statement

Let $P(z)=\sum_{1\leq k\leq n}a_kz^k$ for some $a_k\in \mathbb{C}$ with $|a_k|=1$ for $1\leq k\leq n$. Does there exist a constant $c>0$ such that, for $n\geq 2$, we have $\max_{|z|=1}|P(z)| \geq (1+c)\sqrt{n}$?

## Status

**DISPROVED**

This was a conjecture of Erdős and Newman.

## Key Results

- **Lower bound**: The trivial bound of $\sqrt{n}$ follows from Parseval's theorem
- **Körner [Ko80]**: Constructed polynomials where $(c_1-o(1))\sqrt{n} \leq |P(z)| \leq (c_2+o(1))\sqrt{n}$ for absolute constants $0<c_1\leq c_2$
- **Kahane [Ka80]**: Constructed 'ultraflat' polynomials with $P(z)=(1+o(1))\sqrt{n}$ uniformly on the unit circle, disproving the conjecture
- **Bombieri-Bourgain [BoBo09]**: Improved Kahane's construction to $P(z)=\sqrt{n}+O(n^{7/18}(\log n)^{O(1)})$

## Formalization Details

### Main Components

1. **Main theorem `erdos_230`**: Negation of the conjecture - there does NOT exist a constant $c > 0$ such that all such polynomials have maximum at least $(1+c)\sqrt{n}$

2. **`erdos_230.kahane_ultraflat`**: Kahane's construction achieving $(1+o(1))\sqrt{n}$ uniformly

## Technical Notes

- Polynomials have coefficients with unit modulus on the complex unit circle
- The $o(1)$ term tends to 0 as $n \to \infty$

## References

- [Ko80] Körner, T. W., _On a polynomial of J. S. Byrnes_. Bull. London Math. Soc. (1980), 219-224.
- [Ka80] Kahane, J.-P., _Sur les polynômes à coefficients unimodulaires_. Bull. London Math. Soc. (1980), 321-342.
- [BoBo09] Bombieri, E. and Bourgain, J., _A remark on Bohr's inequality_. Int. Math. Res. Not. IMRN (2009), 4307-4330.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/230.lean`
