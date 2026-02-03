/-
Copyright 2026 The Formal Conjectures Authors.

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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Complex.Basic

/-!
# Erdős Problem 115

*Reference:* [erdosproblems.com/115](https://www.erdosproblems.com/115)
-/

namespace Erdos115

open Classical Complex

/--
If $p(z)$ is a polynomial of degree $n$ such that {z : $\lvert p(z)\rvert\leq 1$} is connected
then is it true that
\[\max_{\substack{z\in\mathbb{C}\\ \lvert p(z)\rvert\leq 1}} \lvert p'(z)\rvert \leq (\tfrac{1}{2}+o(1))n^2?
\]
-/--

def ConnectedLemniscate (p : Polynomial ℂ) : Prop :=
  IsConnected {z : ℂ | ‖p.eval z‖ ≤ 1}

noncomputable def MaxDerivativeOnLemniscate (p : Polynomial ℂ) : ℝ :=
  sSup { y : ℝ | ∃ z : ℂ, ‖p.eval z‖ ≤ 1 ∧ ‖(Polynomial.derivative p).eval z‖ = y }

noncomputable def optimal_constant (n : ℕ) : ℝ :=
  sSup { v : ℝ | ∃ p : Polynomial ℂ, p.degree = n ∧ ConnectedLemniscate p ∧
    MaxDerivativeOnLemniscate p = v }

@[category research open, AMS 30]
theorem erdos_115 : answer(sorry) ↔
  Filter.Tendsto (fun n ↦ optimal_constant n / (n : ℝ)^2) Filter.atTop (nhds (1/2)) ∨
  (Filter.limsup (fun n ↦ optimal_constant n / (n : ℝ)^2) Filter.atTop ≤ 1/2) := by
  sorry

end Erdos115
