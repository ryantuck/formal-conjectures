# Erdős Problem 154 Formalization Log

The problem asks whether the sumset $A+A$ of a Sidon set $A \subset \{1,\dots,N\}$ with $|A| \sim N^{1/2}$ is well-distributed over all small moduli.

## Problem Statement

Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be well-distributed over all small moduli? In particular, must about half the elements of $A+A$ be even and half odd?

## Formalization Details

- **Sidon set**: Formalized using `IsSidon` from `FormalConjecturesForMathlib.Combinatorics.Basic`.
- **Asymptotic equivalence**: $|A| \sim N^{1/2}$ is formalized using `~[atTop]` and `Real.sqrt`.
- **Well-distributed over all small moduli**: Formalized as the property that for any fixed $m > 0$ and $r < m$, the proportion of elements in $A+A$ that are $r \pmod m$ tends to $1/m$ as $N \to \infty$.
- **Even/Odd**: This is the case $m=2$, which is explicitly mentioned in the problem statement and covered by the general case.

## Solved Status

The problem has been solved in the affirmative. Lindström [Li98] showed that $A$ itself is well-distributed, and it's noted that the property for $A+A$ follows from the Sidon property.

## References

- [ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
- [Li98] B. Lindström, "On the distribution of Sidon sets", Discrete Math. 186 (1998), 279–281.
- [Ko99] M. N. Kolountzakis, "The density of Sidon sets and the distribution of their sums", Acta Arith. 89 (1999), 115–127.
