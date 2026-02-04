# Erdős Problem 178 Formalization Log

## Conjecture

Let $A_1,A_2,\ldots$ be an infinite collection of infinite sets of integers, say $A_i=\{a_{i1}<a_{i2}<\cdots\}$. Does there exist some $f:\mathbb{N}	o\{-1,1\}$ such that
$$ \max_{m, 1\leq i\leq d} \left\lvert \sum_{1\leq j\leq m} f(a_{ij})ightvert \ll_d 1 $$
for all $d\geq 1$?

## Formalization

I represented the collection of sets as a function `A : ℕ → ℕ → ℕ`, where `A i j` is the $j$-th element of the $i$-th set.
The condition $a_{i1} < a_{i2} < \dots$ is represented by `StrictMono (A i)`.
The bounded condition $\ll_d 1$ is represented by the existence of a constant $C$ for each $d$.

## Status

The conjecture is formalized but not proven. The theorem `erdos_178` has a `sorry` placeholder.
This problem was solved by Beck (1981).
Built successfully using `lake build FormalConjectures/ErdosProblems/178.lean`.
Note: Used `range m` which means indices $0, \dots, m-1$. The problem says $1 \leq j \leq m$, which is $m$ terms.
I interpreted `A i j` as starting from $j=0$.
