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
# Erdős Problem 256

*Reference:* [erdosproblems.com/256](https://www.erdosproblems.com/256)
-/

open Complex Filter Topology

namespace Erdos256

/--
Let $n \geq 1$ and $f(n)$ be maximal such that for any integers $1 \leq a_1 \leq \cdots \leq a_n$:
$$\max_{|z|=1}\left|\prod_{i}(1-z^{a_i})\right| \geq f(n)$$

The problem asks to estimate $f(n)$, specifically whether there exists a constant $c > 0$
such that $\log f(n) \gg n^c$.

Key results:
- Erdős and Szekeres (1959): $\lim f(n)^{1/n} = 1$ and $f(n) > \sqrt{2n}$
- Atkinson (1961): $\log f(n) \ll n^{1/2}\log n$
- Odlyzko (1982): $\log f(n) \ll n^{1/3}(\log n)^{4/3}$
- Belov and Konyagin (1996): $\log f(n) \ll (\log n)^4$ (answered negatively)
-/
noncomputable def f (n : ℕ) : ℝ :=
  ⨅ (a : Fin n → ℕ), ⨅ (_ : ∀ i j, i ≤ j → a i ≤ a j), ⨅ (_ : ∀ i, a i ≥ 1),
    ⨆ (z : ℂ), if norm z = 1 then norm (∏ i : Fin n, (1 - z^(a i))) else 0

/--
Erdős and Szekeres proved that $\lim f(n)^{1/n} = 1$.
-/
@[category research solved, AMS 11]
theorem erdos_256.limit_power : Tendsto (fun n : ℕ => (f n)^(1 / (n : ℝ))) atTop (𝓝 1) := by
  sorry

/--
Erdős and Szekeres proved that $f(n) > \sqrt{2n}$.
-/
@[category research solved, AMS 11]
theorem erdos_256.lower_bound (n : ℕ) (hn : n ≥ 1) : f n > Real.sqrt (2 * (n : ℝ)) := by
  sorry

/--
Belov and Konyagin (1996) answered the main question negatively:
$\log f(n) \ll (\log n)^4$, so there is no $c > 0$ with $\log f(n) \gg n^c$.
-/
@[category research solved, AMS 11]
theorem erdos_256 : ¬ ∃ c > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 1 →
    Real.log (f n) ≥ C * (n : ℝ)^c := by
  sorry

/--
Belov and Konyagin's upper bound: $\log f(n) \ll (\log n)^4$.
-/
@[category research solved, AMS 11]
theorem erdos_256.belov_konyagin : ∃ C > 0, ∀ n : ℕ, n ≥ 2 →
    Real.log (f n) ≤ C * (Real.log (n : ℝ))^4 := by
  sorry

end Erdos256
