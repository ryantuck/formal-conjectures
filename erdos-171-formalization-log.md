# Erdős Problem 171 Formalization Log

## Conjecture

Is it true that for every $\epsilon > 0$ and integer $t \geq 1$, if $N$ is sufficiently large and $A$ is a subset of $[t]^N$ of size at least $\epsilon t^N$ then $A$ must contain a combinatorial line $P$ (a set $P=\{p_1,\dots,p_t\}$ where for each coordinate $1 \leq j \leq N$ the $j$th coordinate of $p_i$ is either $i$ or constant).

## Formalization

I defined `IsCombinatorialLine` to represent a combinatorial line in $(Fin\ t)^N$. A set $L$ of points is a combinatorial line if there is a non-empty set of active coordinates $S$ such that for all $j \in S$, the $j$-th coordinate of the $i$-th point in $L$ is $i$, and for all $j 
otin S$, the $j$-th coordinate is constant across all points in $L$.

The theorem `erdos_171` states that for any $t \geq 1$ and $\epsilon > 0$, for sufficiently large $N$, any subset $A \subseteq (Fin\ t)^N$ with density at least $\epsilon$ contains a combinatorial line.

## Status

The conjecture is formalized but not proven. This is known as the Density Hales-Jewett theorem, proved by Furstenberg and Katznelson in 1991. The theorem `erdos_171` has a `sorry` placeholder.
