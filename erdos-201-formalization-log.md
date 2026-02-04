# Erdős Problem 201 Formalization Log

## Problem Statement

Let $G_k(N)$ be such that any set of $N$ integers contains a subset of size at least $G_k(N)$ which does not contain a $k$-term arithmetic progression. Determine the size of $G_k(N)$. How does it relate to $R_k(N)$, the size of the largest subset of $\{1,\dots,N\}$ without a $k$-term arithmetic progression? Is it true that
$$ \lim_{N	o \infty}\frac{R_3(N)}{G_3(N)}=1? $$

## Discovery and Analysis

- $R_k(N)$ is the standard $r_k(N)$, the maximum size of a $k$-AP-free subset of $\{1, \dots, N\}$.
- $G_k(N)$ is defined as the maximum $M$ such that every set $A \subseteq \mathbb{Z}$ with $|A|=N$ has a $k$-AP-free subset $B \subseteq A$ with $|B| \ge M$.
- This is equivalent to $G_k(N) = \min_{A \subseteq \mathbb{Z}, |A|=N} \max \{ |B| : B \subseteq A, B 	ext{ is } k	ext{-AP free} \}$.
- It is trivial that $G_k(N) \le R_k(N)$ since $\{1, \dots, N\}$ is one possible set of size $N$.
- Riddell (1969) first investigated this. For example, $G_3(5)=3$ (witnessed by $\{0, 1, 2, 3, 6\}$) while $R_3(5)=4$ (witnessed by $\{1, 2, 4, 5\}$).
- Komlós, Sulyok, and Szemerédi (1975) showed that $G_k(N) = \Theta_k(R_k(N))$.
- The specific conjecture is whether the ratio tends to 1 for $k=3$.

## Formalization Plan

- Use `Set.IsAPOfLengthFree.maxCard` for $R_k(N)$.
- Define $G_k(N)$ using `sInf` over all `Finset ℤ` of size $N$, and `sSup` over subsets that are `IsAPOfLengthFree`.
- State the limit conjecture using `Tendsto` and `𝓝 1`.

## Lean Implementation Details

- `G k N` is defined as `sInf { (sSup {Finset.card B | B ⊆ A ∧ B.toSet.IsAPOfLengthFree k}) | A : Finset ℤ, A.card = N }`.
- The conjecture is stated for $k=3$.

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/201.lean`.
