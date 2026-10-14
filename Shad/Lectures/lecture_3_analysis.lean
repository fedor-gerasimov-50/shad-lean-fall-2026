import Mathlib

/-
# Анализ в Mathlib

План:
0. Иерархия тайпклассов
1. Пределы (фильтры)
2. Производные
3. Суммы и ряды
4. Мера и интеграл
-/

open Filter Topology MeasureTheory





/- ## 0. Иерархия тайпклассов -/

/- Цель: доказать теорему один раз в общем виде и применять в частных случаях. -/

example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  apply add_sq

example (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  apply add_sq

example (x y : ℂ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  exact add_sq x y

#check add_sq

/-
Иерархия:

  CommSemiring
  ├─ Semiring              дистрибутивность, `0 * a = 0`
  │  ├─ AddCommMonoid      `+`, `0`, `a + b = b + a`
  │  │  └─ AddMonoid
  │  │     └─ AddSemigroup
  │  │        └─ Add
  │  └─ MonoidWithZero
  │     └─ Monoid          `*`, `1`
  │        └─ Semigroup
  │           └─ Mul
  └─ CommMonoid            `a * b = b * a`
     └─ Monoid
-/
#check CommSemiring

/- ### Игрушечный пример -/

namespace Toy1

-- Класс `Group`: контракт которому обязана удовлетворять каждая группа
class Group (G : Type*) where
  add : G → G → G
  zero : G
  neg : G → G
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  neg_add_cancel : ∀ a, add (neg a) a = zero

-- Инстанс нужен чтобы показать Lean какая на `ℤ` структура группы
-- Нужно показать как определены операции и доказать что они удовлетворяют законам группы
instance : Group ℤ where
  add := fun a b ↦ a + b
  zero := 0
  neg := fun a ↦ -a
  add_assoc := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind

-- 0 + a = a
example (a : ℤ) : Group.add Group.zero a = a := by
  exact Group.zero_add a

-- неудобно: нет нотации

end Toy1

namespace Toy2



-- операции берём из классов `Add`, `Zero`, `Neg` -- получаем нотацию `+`, `0`, `-`
class Group (G : Type*) extends Add G, Zero G, Neg G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
  zero_add : ∀ a : G, 0 + a = a
  add_zero : ∀ a : G, a + 0 = a
  neg_add_cancel : ∀ a : G, -a + a = 0

-- `+`, `0`, `-` на `ℤ` уже есть (берутся из инстансов для `Add ℤ`, `Zero ℤ`, `Neg ℤ`),
-- осталось доказать аксиомы
instance : Group ℤ where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg

theorem zero_unique {G : Type*} [Group G] (e : G) (h : ∀ a, e + a = a) : e = 0 := by
  have := h 0
  rw [Group.add_zero] at this
  exact this


theorem zero_unique' (e : ℤ) (h : ∀ a, e + a = a) : e = 0 := by
  have := h 0
  rw [Group.add_zero] at this
  exact this

-- расширяем наш класс, требуя еще коммутативности
class CommGroup (G : Type*) extends Group G where
  add_comm : ∀ a b : G, a + b = b + a

instance : CommGroup ℤ where
  add_comm := Int.add_comm

-- Инстансы могут сами иметь тайпклассовые аргументы:
-- декартово произведение
instance {X Y : Type*} [Group X] [Group Y] : Group (X × Y) where
  add_assoc a b c := by
    ext
    · exact Group.add_assoc a.1 b.1 c.1
    · exact Group.add_assoc a.2 b.2 c.2
  zero_add a := by
    ext
    · exact Group.zero_add a.1
    · exact Group.zero_add a.2
  add_zero a := by
    ext
    · exact Group.add_zero a.1
    · exact Group.add_zero a.2
  neg_add_cancel a := by
    ext
    · exact Group.neg_add_cancel a.1
    · exact Group.neg_add_cancel a.2

-- функции с поточечными операциями
instance {X Y : Type*} [Group X] : Group (Y → X) where
  add_assoc a b c := by
    ext y
    exact Group.add_assoc (a y) (b y) (c y)
  zero_add a := by
    ext y
    exact Group.zero_add (a y)
  add_zero a := by
    ext y
    exact Group.add_zero (a y)
  neg_add_cancel a := by
    ext y
    exact Group.neg_add_cancel (a y)

-- так можно проверить синтезирутся ли нужный инстанс
#synth Group ℤ
#synth Group (ℤ × ℤ)
#synth Group (ℕ → ℤ)
#synth Group (ℕ → ℤ × (ℝ → ℤ)) -- A → B

example (e : ℤ) (h : ∀ a, e + a = a) : e = 0 := zero_unique e h
example (e : ℤ × ℤ) (h : ∀ a, e + a = a) : e = 0 := zero_unique e h
example (e : ℕ → ℤ) (h : ∀ a, e + a = a) : e = 0 := zero_unique e h
example {Y : Type*} (e : Y → ℤ) (h : ∀ a, e + a = a) : e = 0 := zero_unique e h

end Toy2

/- ### Тактики тоже используют тайпклассы -/

-- `ring`: любое коммутативное (полу)кольцо
example {R : Type*} [CommRing R] (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

-- `abel`: любая абелева группа
example {G : Type*} [AddCommGroup G] (a b : G) : a + b - a = b := by
  abel

-- `linarith`: любое упорядоченное поле
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (x y : K) (h : x < y) :
    x < (x + y) / 2 := by
  linarith

/- ### Иерархия классов в анализе -/

/-
  TopologicalSpace X        открытые множества
        ↑
  UniformSpace X            равномерная структура
        ↑
  PseudoMetricSpace X       `dist`
        ↑
  MetricSpace X             `dist x y = 0 → x = y`
        ↑
  NormedAddCommGroup E      `‖x‖`, `dist x y = ‖x - y‖`
        +
  NormedSpace 𝕜 E           `‖c • x‖ ≤ ‖c‖ * ‖x‖`
        +
  InnerProductSpace 𝕜 E     `⟪x, y⟫`

Свойства: `T2Space`, `CompleteSpace`, `CompactSpace`, `ProperSpace`, ...
-/
#check InnerProductSpace

-- лемма для любой нормированной группы ...
theorem my_norm_sub_norm_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
  have := norm_add_le (x - y) y
  simp at this
  linarith

-- ... применяется к `ℝ` ...
example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  apply my_norm_sub_norm_le a b

-- ... и к `ℂ`
example (z w : ℂ) : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := my_norm_sub_norm_le z w

-- Теорема Вейерштрасса: любое топологическое пространство
#check IsCompact.exists_isMinOn


-- Icc [a, b]
-- Ioc (a, b]
-- Ico [a, b)
-- Ici [a, ∞)
-- Iic (-∞, c]

-- отрезок в `ℝ`
example (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, f x ≤ f y := by
  obtain ⟨x, hx, hmin⟩ := by
    apply IsCompact.exists_isMinOn _ _ hf.continuousOn
    · exact Set.Icc 0 1
    · exact isCompact_Icc
    · rw [Set.nonempty_Icc]
      norm_num
  exact ⟨x, hx, hmin⟩

-- круг в `ℂ`
example (f : ℂ → ℝ) (hf : Continuous f) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, f z ≤ f w := by
  obtain ⟨z, hz, hmin⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn ⟨0, by simp⟩ hf.continuousOn
  exact ⟨z, hz, hmin⟩





/- ## 1. Пределы -/

/-
Сколько разных видов пределов в курсе матанализа?
* `aₙ → a` при `n → ∞`
* `f x → b` при `x → a`
* `f x → b` при `x → a`, `x ≠ a` (проколотая окрестность)
* `f x → b` при `x → a+` (односторонние)
* `f x → b` при `x → +∞`
* `f x → +∞` при ...
* `fₙ x → f x` почти всюду по мере
* ... и всё это для функций `ℝ → ℝ`, `ℝ → ℂ`, `ℝⁿ → ℝᵐ`, ...

Если для каждой пары "откуда/куда" заводить своё определение, то придётся
для каждой пары отдельно доказывать "предел суммы равен сумме пределов" и т.д.

Решение Mathlib: *фильтры*. Есть одно определение предела:

  `Filter.Tendsto f l₁ l₂`

где `l₁ : Filter α` описывает "куда стремится аргумент", а `l₂ : Filter β` --
"куда стремится значение".
-/

#check Filter
#check Tendsto

#check Tendsto (fun x ↦ x / (x + 1)) atTop (𝓝 1)

-- примеры фильтров
#check (atTop : Filter ℕ)          -- `n → ∞`: множества, содержащие хвост `{n | n ≥ N}`
#check (atTop : Filter ℝ)          -- `x → +∞`
#check (atBot : Filter ℝ)          -- `x → -∞`
#check (𝓝 (2 : ℝ))                -- `x → 2`: множества, содержащие окрестность `2`
#check (𝓝[≠] (2 : ℝ))             -- `x → 2`, `x ≠ 2`: проколотая окрестность
#check (𝓝[>] (0 : ℝ))             -- `x → 0+`: правая полуокрестность
#check (𝓝[Set.Icc 0 1] (0 : ℝ))   -- `x → 0`, `x ∈ [0, 1]`
#check (𝓟 (Set.Icc (0 : ℝ) 1))    -- все надмножества `[0, 1]` (главный фильтр)
#check (ae (volume : Measure ℝ))   -- "почти всюду": множества, дополнение которых меры `0`

/-
### Что такое фильтр

`l : Filter α` -- некоторое множество "окрестностей" в `α`:
* `univ ∈ l`                      -- всё `α` это окрестность
* `s ∈ l`, `s ⊆ t` ⇒ `t ∈ l`     -- расширив окрестность мы получим окрестность
* `s ∈ l`, `t ∈ l` ⇒ `s ∩ t ∈ l` -- пересекая окрестности, мы получим окрестность

-- X ⊆ Y ==> 𝓟 Y ⊆ 𝓟 X ==> 𝓟 X ≤ 𝓟 Y

Операции:
* `l₁ ≤ l₂` -- каждая окрестность из `l₂` является окрестностью в `l₁` (`l₁` "мельче")
* `map f l` -- образ: `s` -- окрестность в `map f l`, если `f ⁻¹' s` -- окрестность в `l`
* `l₁ ×ˢ l₂` -- окрестности содержат `s ×ˢ t`, где `s ∈ l₁`, `t ∈ l₂`;
  `𝓝 (a, b) = 𝓝 a ×ˢ 𝓝 b`

`Tendsto f l₁ l₂ := map f l₁ ≤ l₂`
-/

#check Tendsto (fun x ↦ x / (x + 1)) atTop (𝓝 1)

/-
Почему так: `Tendsto f l₁ l₂` ⇔ `∀ s ∈ l₂, f ⁻¹' s ∈ l₁`,
"прообраз любой окрестности из `l₂` -- окрестность из `l₁`" (как в определении непрерывности).
* `atTop`, `𝓝 a`: окрестности `atTop` -- множества, содержащие луч `[N, ∞)`.
  Для любой окрестности `U ∋ a` найдётся `N`: `u n ∈ U` при `n ≥ N`
* `𝓝 x₀`, `𝓝 a`: для любой окрестности `U ∋ a` найдётся окрестность `V ∋ x₀`: `f '' V ⊆ U`
-/

-- f₁ ≤ f₂ ==> map F f₁ ≤ map F f₂

-- композиция пределов: `map` + монотонность
theorem my_tendsto_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (hg : Tendsto g lb lc) (hf : Tendsto f la lb) : Tendsto (g ∘ f) la lc := by
  unfold Tendsto at *
  rw [← Filter.map_map]
  grw [hf]
  assumption

-- предел суммы: любой фильтр `l`, любое `M` с непрерывным сложением
-- `x ↦ f x + g x` = `(+) ∘ (x ↦ (f x, g x))`
theorem my_tendsto_add {α M : Type*} [TopologicalSpace M] [Add M] [ContinuousAdd M]
    {l : Filter α} {f g : α → M} {a b : M}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x ↦ f x + g x) l (𝓝 (a + b)) := by
  -- `(f x, g x) → (a, b)`
  have h₁ : Tendsto (fun x ↦ (f x, g x)) l (𝓝 a ×ˢ 𝓝 b) := hf.prodMk hg
  rw [← nhds_prod_eq] at h₁
  -- `+` непрерывно в `(a, b)`
  have h₂ : Tendsto (fun p : M × M ↦ p.1 + p.2) (𝓝 (a, b)) (𝓝 (a + b)) :=
    continuous_add.tendsto (a, b)
  exact my_tendsto_comp h₂ h₁

/-
### `Eventually` и `Frequently`

* `∀ᶠ x in l, p x` -- `{x | p x} ∈ l`: `p` верно для "почти всех" точек `l`
* `∃ᶠ x in l, p x` -- `¬ ∀ᶠ x in l, ¬ p x`: `p` верно "сколь угодно часто"
-/
#check Filter.Eventually
#check Filter.Frequently

-- для `atTop`: "для всех достаточно больших" и "для бесконечно многих"
#check Filter.eventually_atTop    -- `∀ᶠ n in atTop, p n ↔ ∃ N, ∀ n ≥ N, p n`
#check Filter.frequently_atTop    -- `∃ᶠ n in atTop, p n ↔ ∀ N, ∃ n ≥ N, p n`
#check Metric.eventually_nhds_iff -- `∀ᶠ x in 𝓝 a, p x ↔ ∃ ε > 0, ∀ x, dist x a < ε → p x`

example : ∀ᶠ n : ℕ in atTop, 100 < n := eventually_gt_atTop 100

example : ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x := eventually_gt_nhds one_pos

-- `∀ᵐ x ∂μ, p x` -- это `∀ᶠ x in ae μ, p x`
-- почти все `x` не равны 0
example : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := Measure.ae_ne volume 0

-- чётные числа встречаются сколь угодно далеко ...
example : ∃ᶠ n : ℕ in atTop, Even n := by
  rw [frequently_atTop]
  intro N
  exact ⟨2 * N, by grind, even_two_mul N⟩

-- ... но не "почти все" числа чётны
example : ¬ ∀ᶠ n : ℕ in atTop, Even n := by
  rw [eventually_atTop]
  rintro ⟨N, hN⟩
  have := hN (2 * N + 1) (by grind)
  simp at this

#check Filter.Eventually.and
#check Filter.Eventually.mono
#check Filter.Eventually.frequently
#check Filter.Frequently.and_eventually

/- ### ε-N -/
#check Metric.tendsto_atTop     -- ε-N
#check Metric.tendsto_nhds_nhds -- ε-δ

example : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  sorry

/-
### Как доказывать: из библиотечных лемм

На практике ε-N почти никогда не нужен: в библиотеке есть пределы стандартных
последовательностей и "арифметика пределов". Обратите внимание, что
`Tendsto.add`, `Tendsto.mul`, ... доказаны для *произвольного* фильтра `l` --
это одна теорема для всех видов пределов сразу.
-/
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check Tendsto.add
#check Tendsto.mul
#check Tendsto.const_mul
#check tendsto_const_nhds
#check Tendsto.comp

example : Tendsto (fun n : ℕ ↦ 3 + 2 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have := (h.const_mul 2).const_add 3
  -- `simpa` упрощает и `this`, и цель, и сравнивает их
  simpa [div_eq_mul_inv] using this

-- предел "в бесконечность" -- тот же `Tendsto`, только с `atTop` справа
example : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop

-- односторонний предел: `1 / x → +∞` при `x → 0+`
example : Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero

/-
### Теорема о двух милиционерах и `filter_upwards`

Неравенства в лемме о двух милиционерах нужны только "в конце" -- для
почти всех точек фильтра. Тактика `filter_upwards [h₁, h₂, ...] with x hx₁ hx₂ ...`
позволяет работать с утверждениями вида `∀ᶠ x in l, ...`:
она сводит цель `∀ᶠ x in l, q x` к `∀ x, p₁ x → p₂ x → ... → q x`.
-/
#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

#eval 1 / 0

example : Tendsto (fun n : ℕ ↦ Real.sin n / n) atTop (𝓝 0) := by
  have h₂ : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h₁ : Tendsto (fun n : ℕ ↦ -(1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using h₂.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂
  · filter_upwards [eventually_gt_atTop 0] with n hn
    sorry
  · filter_upwards [eventually_gt_atTop 0] with n hn
    sorry

/-
### Единственность предела

Посмотрим на предположения теоремы о единственности предела:
-/
#check tendsto_nhds_unique
/-
* `[T2Space X]` -- в нехаусдорфовом пространстве предел может быть не единственным;
* `[l.NeBot]` -- фильтр не "пустой" (`⊥` содержит все множества, включая `∅`,
  и по `⊥` функция стремится к чему угодно).

Тайпклассы позволяют точно указать, что нужно для теоремы, и Lean
сам проверяет эти условия для `ℝ`, `atTop` и т.д.
-/

/-
### Непрерывность

`Continuous f` определена топологически (прообраз открытого открыт),
`ContinuousAt f x` -- это `Tendsto f (𝓝 x) (𝓝 (f x))`.
-/
#check continuous_iff_continuousAt
#check Metric.continuous_iff  -- ε-δ

/-
Для доказательства непрерывности (а также дифференцируемости, измеримости)
"составных" функций есть тактика `fun_prop`.
-/
example : Continuous (fun x : ℝ ↦ Real.sin (x ^ 2) * Real.exp x + 1) := by
  fun_prop

example (f : ℝ → ℝ) (hf : Continuous f) : Continuous (fun x ↦ f (x ^ 3) - Real.cos (f x)) := by
  fun_prop

/- ## 2. Производные -/


-- `f` дифференцируема в `x` и её производная равна `c`
#check HasDerivAt (fun x : ℝ ↦ x ^ 2) 2 1
-- `f` дифференцируема в `x` (`𝕜` указывается явно: `ℝ` или `ℂ`)
#check DifferentiableAt ℂ (fun z : ℂ ↦ z ^ 2) 1
-- *число*, производная `f` в точке `x`
#check deriv (fun x : ℝ ↦ x ^ 2) 1

/-
`deriv` -- тотальная функция: если `f` не дифференцируема в `x`, то
`deriv f x = 0` ("junk value"). Поэтому теоремы про `deriv` обычно
требуют гипотезу о дифференцируемости, а `HasDerivAt` удобнее, когда
производную надо *вычислить*.
-/
#check deriv_zero_of_not_differentiableAt
#check deriv_abs_zero  -- `deriv |·| 0 = 0`, хотя модуль не дифференцируем в нуле
#check HasDerivAt.deriv

/-
### Общее определение

Производная Фреше: `f : E → F` (`E`, `F` -- нормированные пространства над `𝕜`)
дифференцируема в `x`, если есть непрерывное линейное `f' : E →L[𝕜] F` такое, что

  `f (x + h) = f x + f' h + o(‖h‖)` при `h → 0`
-/
#check HasFDerivAt                          -- `f'` -- производная Фреше `f` в точке `x`
#check hasFDerivAt_iff_isLittleO_nhds_zero  -- определение через `o(h)`
#check fderiv                               -- сама производная `fderiv 𝕜 f x : E →L[𝕜] F` (аналог `deriv`)
#check HasDerivAt                           -- частный случай `E = 𝕜`
#check hasDerivAt_iff_hasFDerivAt           -- `f'` ↔ линейное отображение `t ↦ t • f'`
#check hasDerivAt_iff_tendsto_slope         -- привычное определение: предел `(f y - f x) / (y - x)`
#check HasDerivWithinAt                     -- производная по множеству
#check HasStrictDerivAt                     -- строгая производная
#check HasFDerivAtFilter                    -- все варианты выше: производная "вдоль фильтра"

#check hasFDerivAt_ringInverse   -- обратный элемент (матрица): `d(A⁻¹)(H) = -A⁻¹ * H * A⁻¹`
#check hasStrictFDerivAt_norm_sq -- квадрат нормы: `d(‖x‖²)(h) = 2 * ⟪x, h⟫`




/-
### Основные теоремы
-/
#check IsLocalMin.deriv_eq_zero         -- Ферма
#check exists_deriv_eq_zero             -- Ролль
#check exists_deriv_eq_slope            -- Лагранж
#check monotone_of_deriv_nonneg         -- монотонность
#check strictMonoOn_of_deriv_pos        -- строгая монотонность на выпуклом множестве
#check is_const_of_deriv_eq_zero        -- `f' = 0 → f = const`
#check Convex.norm_image_sub_le_of_norm_deriv_le  -- `|f y - f x| ≤ C |y - x|`

-- Пример: `sin x ≤ x` при `x ≥ 0`
example (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x := by
  let f (x : ℝ) := x - Real.sin x
  suffices f 0 ≤ f x by
    simp [f] at this
    exact this
  suffices Monotone f by
    apply this hx
  apply monotone_of_deriv_nonneg
  · fun_prop
  · intro x
    simp [f]
    exact Real.cos_le_one x













/- ## 3. Суммы и ряды -/

/-
### Конечные суммы

`∑ i ∈ s, f i` -- сумма по конечному множеству `s : Finset ι`
(`Finset` -- конечное множество, в отличие от `Set`).
`∑ i, f i` -- сумма по всему конечному типу (`[Fintype ι]`), например `Fin n`.
Всё это работает в любом коммутативном моноиде (`[AddCommMonoid M]`).
-/

#check Finset ℤ

#check Fintype
#synth Fintype Bool

#synth Fintype (Fin 20)

#check Set ℤ
#check Set.Finite {n : ℕ | n < 43}

#check Finset.range 5          -- {0, 1, 2, 3, 4}
#check ∑ i ∈ Finset.range 5, i ^ 2
#check ∑ i : Fin 5, (i : ℕ)

noncomputable def foo (x y : ℝ) : ℝ :=
  if x < y then
    5
  else
    10

example : (3 : ℝ) < 5 := by decide

-- конкретные суммы можно посчитать
example : ∑ i ∈ Finset.range 5, i ^ 2 = 30 := by decide
example : ∑ i ∈ Finset.range 5, i ^ 2 = 30 := by simp [Finset.sum_range_succ]

-- главный инструмент для сумм по `range n` -- индукция + `Finset.sum_range_succ`
#check Finset.sum_range_succ

example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    grind

example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ k * k = (n - 1) * 2 ^ (n + 1) + 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    grind

/-
### Бесконечные суммы

* `HasSum f a` -- "ряд `∑ f i` сходится к `a`";
* `Summable f` -- `∃ a, HasSum f a`;
* `∑' i, f i` (`tsum`) -- сумма ряда, если он сходится, и `0` иначе (мусор!).

Важно: `HasSum f a` -- это *безусловная* сходимость: предел конечных сумм
`∑ i ∈ s, f i` по *всем* конечным множествам `s` (фильтр `atTop` на `Finset ι`).
Поэтому `f` может быть индексирована чем угодно (`ℕ`, `ℤ`, `ℕ × ℕ`, ...),
и сумма не зависит от порядка. В `ℝ` это то же самое, что абсолютная сходимость:
ряд `∑ (-1)ⁿ / (n + 1)` *не* `Summable`!
(В новых версиях Mathlib у `HasSum` есть необязательный аргумент
`SummationFilter`, с помощью которого можно говорить и об условной сходимости,
но по умолчанию сходимость безусловная.)
-/
#print HasSum
#check summable_abs_iff

-- связь с частичными суммами
#check HasSum.tendsto_sum_nat

-- стандартные ряды
#check hasSum_geometric_of_lt_one
#check tsum_geometric_two
#check Real.summable_one_div_nat_pow   -- `∑ 1 / n ^ p` сходится ↔ `1 < p`
#check Real.not_summable_one_div_natCast
#check hasSum_zeta_two                  -- Базельская проблема: `∑ 1 / n ^ 2 = π ^ 2 / 6`

-- признаки сравнения
#check Summable.of_nonneg_of_le
#check Summable.of_norm_bounded

example : Summable fun n : ℕ ↦ Real.sin n / 2 ^ n := by
  apply Summable.of_norm_bounded (g := fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) summable_geometric_two
  intro n
  rw [norm_div, norm_pow, Real.norm_two, div_pow, one_pow,
    div_le_div_iff_of_pos_right (by positivity)]
  exact Real.abs_sin_le_one n

/-
`HasSum` определён для любого топологического коммутативного моноида, а
`Summable.of_norm_bounded` -- для любого полного нормированного пространства.
Поэтому то же самое доказательство работает в `ℂ`:
-/
example : Summable fun n : ℕ ↦ Complex.exp (n * Complex.I) / 2 ^ n := by
  apply Summable.of_norm_bounded (g := fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) summable_geometric_two
  intro n
  have := Complex.norm_exp_ofReal_mul_I n
  push_cast at this
  rw [norm_div, norm_pow, Complex.norm_two, this]
  simp

/-
В `ℝ≥0∞` (`ENNReal`, неотрицательные вещественные числа с `∞`) любой ряд
сходится. Это удобно в теории меры: `μ (⋃ i, s i) = ∑' i, μ (s i)`
не требует никаких условий сходимости.
-/
#check ENNReal.summable




example : HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n / n ^ 2) (-Real.pi ^ 2 / 12) := by
  sorry

/- ## 4. Мера и интеграл -/

/- ### Мера -/
#check MeasurableSpace        -- σ-алгебра на `α` (тоже тайпкласс!)
#check Measure                -- мера: применяется к *любому* множеству (внешняя мера), значения в `ℝ≥0∞`
#check MeasureSpace           -- тип с выделенной мерой `volume`
#check (volume : Measure ℝ)   -- на `ℝ` (и `ℝⁿ`) -- мера Лебега
#check Real.volume_Icc

example : volume (Set.Icc (0 : ℝ) 2) = 2 := by simp

-- счётные множества имеют меру нуль (в пространствах, где точки имеют меру нуль)
example : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
  (Set.countable_range _).measure_zero _

/-
`∀ᵐ x ∂μ, p x` -- это `∀ᶠ x in ae μ, p x`, где фильтр `ae μ` состоит из
множеств с дополнением меры нуль. Поэтому всё, что мы знаем о фильтрах,
работает и здесь -- например, `filter_upwards`:
-/
example (f g : ℝ → ℝ) (h₁ : ∀ᵐ x, f x ≤ g x) (h₂ : ∀ᵐ x, g x ≤ 0) : ∀ᵐ x, f x ≤ 0 := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  linarith

/-
### Интегралы

* `∫⁻ x, f x ∂μ` -- интеграл Лебега для `f : α → ℝ≥0∞`. Всегда определён
  (может быть `∞`).
* `∫ x, f x ∂μ` -- интеграл Бохнера для `f : α → E`, где `E` -- любое банахово
  пространство (`ℝ`, `ℂ`, `ℝⁿ`, ...). Если `f` не интегрируема, то он
  равен `0` (мусор!). `∫ x, f x` -- по мере `volume`.
* `∫ x in s, f x ∂μ` -- интеграл по множеству (= по мере `μ.restrict s`).
* `∫ x in a..b, f x` -- ориентированный интеграл по отрезку:
  `∫ x in a..b, f x = - ∫ x in b..a, f x`.

Интегрируемость: `Integrable f μ` (измеримость + конечность `∫⁻ ‖f‖`) и
`IntervalIntegrable f μ a b`. Непрерывная функция интегрируема на отрезке.
-/
#check Integrable
#check integral_undef
#check intervalIntegral.integral_of_le
#check Continuous.intervalIntegrable

/-
### Вычисление

Для простых интегралов есть готовые леммы (`integral_pow`, `integral_sin`, ...),
их удобно передавать в `norm_num` / `simp`.
-/
example : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  norm_num [integral_pow]

example : ∫ x in (0 : ℝ)..Real.pi, Real.sin x = 2 := by
  norm_num [integral_sin]

/-
В общем случае -- формула Ньютона-Лейбница. Здесь видно, зачем нужна
`HasDerivAt`: для применения формулы нужно предъявить первообразную.
-/
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_deriv_eq_sub

example : ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x ↦ Real.exp (x ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
    intro x _
    apply (hasDerivAt_pow 2 x).exp.congr_deriv
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp
  · -- интегрируемость: функция непрерывна
    apply Continuous.intervalIntegrable
    fun_prop

/-
### Оценки
-/
#check intervalIntegral.integral_nonneg
#check intervalIntegral.integral_mono_on
#check norm_integral_le_integral_norm

example : 0 ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x _
  positivity

/-
### Общность

Один и тот же `∫` работает для любой меры. Например, интеграл по мере Дирака
`δₐ` -- это значение в точке, а по считающей мере на конечном типе -- сумма.
Математическое ожидание случайной величины в Mathlib -- это тоже `∫ ω, X ω ∂ℙ`.
-/
example (f : ℝ → ℝ) (a : ℝ) : ∫ x, f x ∂(Measure.dirac a) = f a := by simp
#check integral_count

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : 0 ≤ f)
    (hi : Integrable f μ) (c : ℝ) (hc : 0 < c) :
    c * μ.real {x | c ≤ f x} ≤ ∫ x, f x ∂μ := by
  sorry


example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[volume] g) :
    f = g := by
  sorry

/-
### Как устроен интеграл Бохнера

простые функции → `L¹` (продолжение по непрерывности) → все функции (`0`, если не интегрируема)
-/
#check SimpleFunc                     -- `α →ₛ E`: измеримая функция с конечным числом значений
#check SimpleFunc.integral             -- `∑ v ∈ f.range, μ (f ⁻¹' {v}) • v`
#check L1.SimpleFunc.integralCLM      -- то же как непрерывное линейное отображение на `L¹`
#check Lp.simpleFunc.denseRange       -- простые функции плотны в `L¹`...
#check L1.integralCLM                 -- ...поэтому интеграл продолжается на всё `L¹`
#check integral_def                   -- `∫ f = if Integrable f μ then L1.integral f else 0`

-- доказательства "по построению": индикаторы → суммы → замыкание в `L¹` → равенство п.в.
#check Integrable.induction

-- непрерывный линейный оператор коммутирует с интегралом
-- (в Mathlib: `ContinuousLinearMap.integral_comp_comm`)
example {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {f : α → E} (hf : Integrable f μ) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  refine Integrable.induction (P := fun f ↦ ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ)) ?_ ?_ ?_ ?_ hf
  · -- индикаторы: `∫ L (1ₛ c) = μ(s) • L c = L (∫ 1ₛ c)`
    intro c s hs _
    have : (fun x ↦ L (s.indicator (fun _ ↦ c) x)) = s.indicator (fun _ ↦ L c) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    simp only [this, integral_indicator_const _ hs, map_smul]
  · -- суммы: линейность
    intro f g _ hf hg hPf hPg
    simp only [Pi.add_apply, map_add]
    rw [integral_add (L.integrable_comp hf) (L.integrable_comp hg), integral_add hf hg, hPf, hPg,
      map_add]
  · -- замкнутость в `L¹`: обе части непрерывны по `f`
    apply isClosed_eq
    · have : (fun f : Lp E 1 μ ↦ ∫ x, L (f x) ∂μ) = fun f ↦ ∫ x, L.compLp f x ∂μ := by
        funext f
        exact integral_congr_ae ((L.coeFn_compLp f).mono fun x hx ↦ hx.symm)
      rw [this]
      exact continuous_integral.comp (L.compLpL 1 μ).continuous
    · exact L.continuous.comp continuous_integral
  · -- равные п.в. функции
    intro f g hfg _ hPf
    rw [← integral_congr_ae hfg, ← hPf]
    exact integral_congr_ae (hfg.fun_comp L).symm
