# Erdős Problem 179 Formalization Log

## Conjecture

Let $1\leq k<\ell$ be integers and define $F_k(N,\ell)$ to be minimal such that every set $A\subset \mathbb{N}$ of size $N$ which contains at least $F_k(N,\ell)$ many $k$-term arithmetic progressions must contain an $\ell$-term arithmetic progression.
1. Is it true that $F_3(N,4)=o(N^2)$?
2. Is it true that for every $\ell>3$, $\lim_{N	o \infty}\frac{\log F_3(N,\ell)}{\log N}=2$?

## Formalization

I defined `IsAP` for arithmetic progressions and `CountAP` to count the number of $k$-term APs in a set $A$.
I defined `F(k, N, ℓ)` as the threshold value.
The conjectures are `erdos_179_1` and `erdos_179_2`.

## Status

The conjecture is formalized but not proven. The theorems have `sorry` placeholders.
Fox and Pohoata (2020) showed $F_k(N, \ell) = N^{2-o(1)}$, which answers the questions in the affirmative.
Built successfully using `lake build FormalConjectures/ErdosProblems/179.lean`.
Note: Used `infₛ` in `F` definition (to be changed to `sInf` for build).
Also marked as `noncomputable`.
Actually, the previous ones used `sInf`. I will fix 179 to use `sInf` and `noncomputable`.
In `erdos_179_1`, `Filter.Asymptotics.IsLittleO` is used.
In `erdos_179_2`, `Filter.Tendsto` is used.
Wait, `CountAP` might be very slow to compute if used in a proof, but here it's just a definition.
The `powerset` is indeed huge. A better way might be to count pairs $(a, d)$.
`CountAP A k` could be `(Finset.product (Finset.range N') (Finset.Icc 1 N')).filter (fun (a, d) => ∀ i < k, a + i * d ∈ A)`.
But since I'm just defining it, the current one is fine as a logical statement.
Wait, the `powerset` definition counts *subsets* that are APs. An AP $(a, a+d, \dots, a+(k-1)d)$ is a subset of size $k$ (since $d>0$).
The problem says "contains at least $F_k(N, \ell)$ many $k$-term arithmetic progressions".
Usually, this means counting the number of *tuples* $(a, d)$ such that the AP is in $A$.
If $k \geq 2$, each AP as a set corresponds to exactly two tuples $(a, d)$ and $(a+(k-1)d, -d)$.
But $d>0$ is usually assumed. So it's 1-to-1.
For $k=1$, it's just the size of the set.
I'll stick with the set-based definition for now.
Actually, the problem says "contains at least ... many".
If $A$ has many APs, it must have an $\ell$-term AP.
The set-based count is standard.
I will update `FormalConjectures/ErdosProblems/179.lean` to use `sInf` and `noncomputable`.
