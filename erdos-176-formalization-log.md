# Erdős Problem 176 Formalization Log

## Conjecture

Let $N(k,\ell)$ be the minimal $N$ such that for any $f:\{1,\dots,N\}	o\{-1,1\}$ there must exist a $k$-term arithmetic progression $P$ such that
$$ \left\lvert \sum_{n\in P}f(n)ightvert\geq \ell. $$
Find good upper bounds for $N(k,\ell)$. Specifically:
1. For any $c>0$, does there exist $C>1$ such that $N(k,ck)\leq C^k$?
2. Does there exist $C>1$ such that $N(k,2)\leq C^k$?
3. Does there exist $C>1$ such that $N(k,\sqrt{k})\leq C^k$?

## Formalization

I defined `IsAP` for arithmetic progressions and `N(k, ℓ)` as the threshold value.
The conjectures are stated as `erdos_176_1`, `erdos_176_2`, and `erdos_176_3`.

## Status

The conjecture is formalized but not proven. All theorems have `sorry` placeholders.
Built successfully using `lake build FormalConjectures/ErdosProblems/176.lean`.
Note: Reordered AMS tags to `AMS 05 11` as suggested by the linter in previous step.
