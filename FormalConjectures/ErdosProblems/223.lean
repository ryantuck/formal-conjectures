/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 223

*Reference:* [erdosproblems.com/223](https://www.erdosproblems.com/223)
-/

open Finset EuclideanGeometry

namespace Erdos223

/--
The diameter of a finite set of points in $\mathbb{R}^d$.
-/
noncomputable def diameter {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ (x ∈ A) (y ∈ A), dist x y

/--
The number of unordered pairs of points in $A$ with distance 1.
-/
noncomputable def countUnitDistances {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (A.offDiag.filter (fun p ↦ dist p.1 p.2 = 1)).card / 2

/--
The maximal number of unit distances in a set of $n$ points in $\mathbb{R}^d$ with diameter $\le 1$.
-/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (A : Finset (EuclideanSpace ℝ (Fin d))),
    if A.card = n ∧ diameter A ≤ 1 then countUnitDistances A else 0

/--
Hopf and Pannwitz [HoPa34] proved $f_2(n) = n$.

[HoPa34] Hopf, H. and Pannwitz, E., _Aufgabe Nr. 167_.
  Jahresbericht Deutsch. Math.-Verein. (1934), 114.
-/
@[category research solved, AMS 52]
theorem erdos_223.f2 : ∀ n ≥ 3, f 2 n = n := by
  sorry

/--
Grünbaum [Gr56], Heppes [He56], and Strasziewicz [St57] independently showed that $f_3(n) = 2n-2$.

[Gr56] Grünbaum, B., _A proof of Vázsonyi's conjecture_.
  Bull. Res. Council Israel. Sect. A (1956), 77-78.

[He56] Heppes, A., _Beweis einer Vermutung von A. Vázsonyi_.
  Acta Math. Acad. Sci. Hungar. (1956), 463-466.

[St57] Strasziewicz, S., _Sur un problème géométrique de P. Erdős_.
  Bull. Acad. Polon. Sci. Cl. III (1957), 39-40.
-/
@[category research solved, AMS 52]
theorem erdos_223.f3 : ∀ n ≥ 4, f 3 n = 2 * n - 2 := by
  sorry

/--
Erdős [Er60b] proved that, for $d \ge 4$, $f_d(n) = (\frac{p-1}{2p} + o(1))n^2$
where $p = \lfloor d/2 \rfloor$.

[Er60b] Erdős, P., _On sets of distances of $n$ points in Euclidean space_.
  Magyar Tud. Akad. Mat. Kutató Int. Közl. (1960), 165-169.
-/
@[category research solved, AMS 52]
theorem erdos_223.fd : ∀ d ≥ 4,
    ∃ r : ℕ → ℝ, r =o[Filter.atTop] (fun n ↦ (n : ℝ)^2) ∧
      ∀ n, (f d n : ℝ) = (((d : ℝ) / 2 - 1) / ((d : ℝ) / 2 * 2)) * (n : ℝ)^2 + r n := by
  sorry

end Erdos223
