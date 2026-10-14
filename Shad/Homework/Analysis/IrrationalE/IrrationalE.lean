import Mathlib
/-!
# Иррациональность `e`

В этой задаче предлагается доказать, что число `e` иррационально.

План: пусть `e = p / d`. Возьмём `q = d + 1 ≥ 2` и умножим ряд `e = ∑ 1 / k!` на `q!`:

  `q! * e = ∑_{k ≤ q} q! / k! + ∑_{k > q} q! / k!`.

Левая часть и первая сумма -- целые числа, а хвост лежит строго между `0` и `1`:

  `∑_{k > q} q! / k! < 1 / q + 1 / q ^ 2 + ... = 1 / (q - 1) ≤ 1`.

Хвост ряда записан как `∑' j, q! / (j + (q + 1))!` -- в такой форме он получается
из `Summable.sum_add_tsum_nat_add`.

В доказательствах можно пользоваться предыдущими пунктами. Пункт засчитывается, только если
доказаны все пункты, на которые он опирается.
-/

/-- **(10 баллов)**

Хвост ряда сходится.

Подсказка: `Real.summable_pow_div_factorial`, `summable_nat_add_iff`. -/
theorem summable_tail (q : ℕ) :
    Summable fun j : ℕ ↦ (q.factorial : ℝ) / (j + (q + 1)).factorial := by
  sorry

/-- **(15 баллов)**

Сравнение членов хвоста с геометрической прогрессией: `q! / (q + 1 + j)! < 1 / q ^ (j + 1)`.

Подсказка: `Nat.factorial_mul_pow_le_factorial`. -/
theorem factorial_div_lt (q j : ℕ) (hq : 1 ≤ q) :
    (q.factorial : ℝ) / (j + (q + 1)).factorial < 1 / q ^ (j + 1) := by
  sorry

/-- **(25 баллов)**

Хвост меньше `1` при `q ≥ 2`: он строго меньше суммы прогрессии `∑ 1 / q ^ (j + 1) = 1 / (q - 1)`.

Подсказка: `Summable.tsum_lt_tsum_of_nonneg`, `tsum_geometric_of_lt_one`. -/
theorem tail_lt_one (q : ℕ) (hq : 2 ≤ q) :
    ∑' j : ℕ, (q.factorial : ℝ) / (j + (q + 1)).factorial < 1 := by
  sorry

/-- **(10 баллов)**

Хвост положителен.

Подсказка: тактика `positivity`. -/
theorem tail_pos (q : ℕ) :
    0 < ∑' j : ℕ, (q.factorial : ℝ) / (j + (q + 1)).factorial := by
  sorry

/-- **(15 баллов)**

`n! * ∑_{k ≤ n} 1 / k!` -- целое число.

Подсказка: `Nat.factorial_dvd_factorial`, `Nat.cast_div`. -/
theorem factorial_mul_sum_int (n : ℕ) :
    ∃ m : ℤ, (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), 1 / (k.factorial : ℝ) = m := by
  sorry

/-- Вспомогательная лемма: `e = ∑ 1 / k!`. -/
lemma exp_one_eq_tsum : Real.exp 1 = ∑' k : ℕ, 1 / (k.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp

/-- **(25 баллов)**

Число `e = exp 1` иррационально.

Подсказка: ряд разбивается на начало и хвост с помощью `Summable.sum_add_tsum_nat_add`;
`q! * (p / d)` -- целое, так как `d ∣ q!` (`Rat.cast_def`, `Nat.dvd_factorial`). -/
theorem exp_one_irrational : Irrational (Real.exp 1) := by
  sorry

-- не забудьте минимизировать импорты
#min_imports
