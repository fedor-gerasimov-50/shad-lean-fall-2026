import Mathlib
/-!
# Метод Ньютона

В этой задаче предлагается доказать сходимость метода Ньютона.

Описание метода можно посмотреть тут: https://ru.algorithmica.org/cs/numerical/newton/
-/

open Filter Topology

/-- Итерации метода Ньютона для `f`, начиная с `x₀`. -/
noncomputable def newton (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => x₀
  | n + 1 =>
    let xₙ := newton f x₀ n
    xₙ - f xₙ / deriv f xₙ

/-- **(100 баллов)**

Пусть `f` выпукла (`f'` монотонна), строго возрастает (`f' > 0`) и `r` -- её корень.
Тогда метод Ньютона сходится к `r` из любой начальной точки `x₀`. -/
theorem newton_tendsto (f : ℝ → ℝ) (r x₀ : ℝ)
    (h_deriv : Differentiable ℝ f) (h_mono : Monotone (deriv f))
    (h_pos : ∀ x, 0 < deriv f x) (hr : f r = 0) :
    Tendsto (newton f x₀) atTop (𝓝 r) := by
  sorry

-- не забудьте минимизировать импорты
#min_imports
