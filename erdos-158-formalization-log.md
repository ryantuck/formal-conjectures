# Erdős Problem 158 Formalization Log

The problem asks whether an infinite $B_2[2]$ set $A$ must satisfy $\liminf_{N 	o \infty} \frac{|A \cap \{1, \dots, N\}|}{N^{1/2}} = 0$.

## Problem Statement

Let $A\subset \mathbb{N}$ be an infinite set such that, for any $n$, there are most $2$ solutions to $a+b=n$ with $a\leq b$. Must
$$\liminf_{N\to\infty}\frac{\lvert A\cap \{1,\ldots,N\rvert}{N^{1/2}}=0?$$

## Formalization Details

- **$B_2[g]$ set**: A set $A \subseteq \mathbb{N}$ is $B_2[g]$ if for all $n$, the equation $a+a' = n, a \leq a', a, a' \in A$ has at most $g$ solutions. Formalized as `B2 g A`.
- **Sidon set**: A $B_2[1]$ set is exactly a Sidon set. This is proven in the API as `b2_one`.
- **Conjecture**: The main conjecture is formalized as `erdos_158.B22`, which states that for any infinite $B_2[2]$ set, the $\liminf$ of the normalized density is 0.
- **Related Results**: The file also includes the known results for Sidon sets ($B_2[1]$):
    - `erdos_158.isSidon'`: A stronger result showing $\liminf |A \cap \{1, \dots, N\}| \cdot N^{-1/2} \cdot (\log N)^{1/2} < \infty$.
    - `erdos_158.isSidon`: The corollary that $\liminf |A \cap \{1, \dots, N\}| \cdot N^{-1/2} = 0$.

## Status

Open for $B_2[2]$ sets. Solved for Sidon ($B_2[1]$) sets.

## References

- [erdosproblems.com/158](https://www.erdosproblems.com/158)
- [ESS94] Erdős, P., Sárközy, A., and Sós, T., "On Sum Sets of Sidon Sets, I", Journal of Number Theory 47 (1994), 329-347.
