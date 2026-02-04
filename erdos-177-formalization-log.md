# Erdős Problem 177 Formalization Log

## Conjecture

Find the smallest $h(d)$ such that the following holds. There exists a function $f:\mathbb{N}	o\{-1,1\}$ such that, for every $d\geq 1$,
$$ \max_{P_d}\left\lvert \sum_{n\in P_d}f(n)ightvert\leq h(d), $$
where $P_d$ ranges over all finite arithmetic progressions with common difference $d$.

## Formalization

I defined `IsAPWithDiff` to represent finite arithmetic progressions with a fixed common difference $d$.
I defined `h(d)` as the infimum of values $c$ such that there exists a colouring with discrepancy at most $c$ for all such APs.

## Status

The conjecture is formalized but not proven. The theorem `erdos_177` has a `sorry` placeholder.
Built successfully using `lake build FormalConjectures/ErdosProblems/177.lean`.
Note: Used `sInf` (rendered as `infₛ`) and marked `h` as `noncomputable`.
In 176, I had to use `sInf` explicitly in the source to avoid "unknown identifier" if the character wasn't recognized, but here I'll see if `infₛ` works or if I need `sInf`. Wait, in 176 it failed with `infₛ`. I should use `sInf`.
Actually, the previous `sed` changed it to `sInf`.
I will update 177 to use `sInf` as well.
