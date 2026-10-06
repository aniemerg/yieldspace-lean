import YieldSpace.Defs

/-! # Theorem 1: non-negative rates -/

namespace YieldSpace

open Real

/-- **Theorem 1.** If `y ≥ x` the fyToken price is at most 1. -/
theorem price_le_one {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hxy : x ≤ y) :
    price t x y ≤ 1 :=
  rpow_le_one (div_nonneg hx.le (hx.trans_le hxy).le)
    ((div_le_one (hx.trans_le hxy)).2 hxy) ht

/-- Both rate notions are non-negative when `y ≥ x`. -/
theorem rate_nonneg {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ rate t x y := by
  unfold rate
  have : 1 ≤ (y / x) ^ t := one_le_rpow ((one_le_div hx).2 hxy) ht
  linarith

theorem paperRate_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : 0 ≤ paperRate x y := by
  unfold paperRate
  have := (one_le_div hx).2 hxy
  linarith

/-- How the two rates relate: `1 + rate = (1 + paperRate) ^ t`. The paper's `r` is the
rate per unit of scaled time; `rate` compounds it over the time to maturity. -/
theorem one_add_rate (t x y : ℝ) : 1 + rate t x y = (1 + paperRate x y) ^ t := by
  simp [rate, paperRate]

/-- `rate` is `1 / price - 1`. -/
theorem rate_eq_inv_price {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    rate t x y = (price t x y)⁻¹ - 1 := by
  simp [rate, price, ← inv_rpow (div_nonneg hx.le hy.le), inv_div]

end YieldSpace
