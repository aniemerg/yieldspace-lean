import YieldSpace.Defs

/-!
# Trades: well-definedness (Thm 4), path independence (Thm 6), scale invariance (Thm 8)

Everything is stated for a generic exponent `a ∈ (0, 1)`, so it covers the fee-free
curve and both fee curves.
-/

namespace YieldSpace

open Real

variable {a : ℝ}

/-! ### Basic facts about `solve` -/

lemma solve_rpow (ha : 0 < a) {k z : ℝ} (h : 0 ≤ k - z ^ a) :
    solve a k z ^ a = k - z ^ a :=
  rpow_inv_rpow h ha.ne'

lemma inv_solve (ha : 0 < a) {k z : ℝ} (h : 0 ≤ k - z ^ a) : inv a (solve a k z) z = k := by
  simp [inv, solve_rpow ha h]

lemma solve_nonneg {k z : ℝ} (h : 0 ≤ k - z ^ a) : 0 ≤ solve a k z := rpow_nonneg h _

lemma solve_pos {k z : ℝ} (h : 0 < k - z ^ a) : 0 < solve a k z := rpow_pos_of_pos h _

/-- Uniqueness: a non-negative reserve that satisfies the invariant is `solve`. -/
lemma eq_solve (ha : 0 < a) {r k z : ℝ} (hr : 0 ≤ r) (h : inv a r z = k) :
    r = solve a k z := by
  rw [solve, ← h, inv, add_sub_cancel_right, rpow_rpow_inv hr ha.ne']

lemma solve_inv_self (ha : 0 < a) {x y : ℝ} (hx : 0 ≤ x) : solve a (inv a x y) y = x :=
  (eq_solve ha hx rfl).symm

/-- `solve` is strictly decreasing in the other reserve. -/
lemma solve_lt_solve (ha : 0 < a) {k z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (h : 0 ≤ k - z' ^ a) : solve a k z' < solve a k z := by
  have : z ^ a < z' ^ a := rpow_lt_rpow hz hzz ha
  exact rpow_lt_rpow h (by linarith) (inv_pos.2 ha)

lemma inv_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ inv a x y :=
  add_nonneg (rpow_nonneg hx _) (rpow_nonneg hy _)

/-- Strict subadditivity of `z ↦ z ^ a` for `0 < a < 1`. -/
lemma rpow_add_lt (_ha0 : 0 < a) (ha1 : a < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x + y) ^ a < x ^ a + y ^ a := by
  have hs : 0 < x + y := add_pos hx hy
  have key : ∀ {u : ℝ}, 0 < u → u < x + y → u / (x + y) * (x + y) ^ a < u ^ a := by
    intro u hu hus
    have h0 : 0 < u / (x + y) := div_pos hu hs
    have h1 : u / (x + y) < 1 := (div_lt_one hs).2 hus
    have : (u / (x + y)) ^ (1 : ℝ) < (u / (x + y)) ^ a :=
      (rpow_lt_rpow_left_iff_of_base_lt_one h0 h1).2 ha1
    rw [rpow_one, div_rpow hu.le hs.le, lt_div_iff₀ (rpow_pos_of_pos hs _)] at this
    exact this
  have h1 := key hx (by linarith)
  have h2 := key hy (by linarith)
  have : x / (x + y) * (x + y) ^ a + y / (x + y) * (x + y) ^ a = (x + y) ^ a := by
    rw [← add_mul, ← add_div, div_self hs.ne', one_mul]
  linarith

/-! ### Theorem 4: well-defined trades

**Output-specified** trades (`inGivenOut`): any `0 ≤ Δ < y` works.

**Input-specified** trades (`outGivenIn`): the curve meets the axis at
`y = k ^ (1/a)`, so the input must satisfy `(y + Δ) ^ a < k`. A simple sufficient
condition is `Δ ≤ x`, i.e. the input is at most the *other* reserve
(`valid_of_le`). -/

/-- Exact domain of an input-specified trade. -/
def Valid (a x y Δ : ℝ) : Prop := (y + Δ) ^ a < inv a x y

/-- An input of at most the opposite reserve is always valid. -/
lemma valid_of_le (ha0 : 0 < a) (ha1 : a < 1) {x y Δ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hΔ0 : 0 ≤ Δ) (hΔx : Δ ≤ x) : Valid a x y Δ := by
  unfold Valid inv
  calc (y + Δ) ^ a ≤ (x + y) ^ a := rpow_le_rpow (by linarith) (by linarith) ha0.le
    _ < x ^ a + y ^ a := rpow_add_lt ha0 ha1 hx hy

lemma Valid.sub_pos {x y Δ : ℝ} (h : Valid a x y Δ) : 0 < inv a x y - (y + Δ) ^ a := by
  unfold Valid at h; linarith

/-- **Theorem 4 (input-specified).** For a valid input `Δ ≥ 0` the output lies in `[0, x)`,
so the new reserve is positive, and the invariant is preserved. -/
theorem outGivenIn_spec (ha : 0 < a) {x y Δ : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hΔ : 0 ≤ Δ)
    (hv : Valid a x y Δ) :
    0 ≤ outGivenIn a x y Δ ∧ 0 < x - outGivenIn a x y Δ ∧
      inv a (x - outGivenIn a x y Δ) (y + Δ) = inv a x y := by
  have hx1 : x - outGivenIn a x y Δ = solve a (inv a x y) (y + Δ) := by
    unfold outGivenIn; ring
  have hle : solve a (inv a x y) (y + Δ) ≤ x := by
    rcases hΔ.eq_or_lt with h | h
    · subst h; rw [add_zero, solve_inv_self ha hx.le]
    · conv_rhs => rw [← solve_inv_self ha hx.le (y := y)]
      exact (solve_lt_solve ha hy (by linarith) hv.sub_pos.le).le
  refine ⟨by linarith, by rw [hx1]; exact solve_pos hv.sub_pos, ?_⟩
  rw [hx1, inv_solve ha hv.sub_pos.le]

/-- Strictly positive output for a strictly positive input. -/
lemma outGivenIn_pos (ha : 0 < a) {x y Δ : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hΔ : 0 < Δ)
    (hv : Valid a x y Δ) : 0 < outGivenIn a x y Δ := by
  have := solve_lt_solve ha (k := inv a x y) hy (by linarith : y < y + Δ) hv.sub_pos.le
  rw [solve_inv_self ha hx.le] at this
  unfold outGivenIn; linarith

/-- **Theorem 4 (input-specified), uniqueness.** Any trade output that keeps the new
reserve non-negative and preserves the invariant equals `outGivenIn`. -/
theorem outGivenIn_unique (ha : 0 < a) {x y Δ d : ℝ} (hd : 0 ≤ x - d)
    (h : inv a (x - d) (y + Δ) = inv a x y) : d = outGivenIn a x y Δ := by
  have := eq_solve ha hd h
  unfold outGivenIn; linarith

/-- **Theorem 4 (output-specified).** For `0 ≤ Δ < y` the required input is
non-negative, the reserves stay positive, and the invariant is preserved. -/
theorem inGivenOut_spec (ha : 0 < a) {x y Δ : ℝ} (hx : 0 < x) (hΔ : 0 ≤ Δ) (hΔy : Δ < y) :
    0 ≤ inGivenOut a x y Δ ∧ 0 < x + inGivenOut a x y Δ ∧ 0 < y - Δ ∧
      inv a (x + inGivenOut a x y Δ) (y - Δ) = inv a x y := by
  have hle : (y - Δ) ^ a ≤ y ^ a := rpow_le_rpow (by linarith) (by linarith) ha.le
  have hxa : 0 < x ^ a := rpow_pos_of_pos hx _
  have hk : 0 ≤ inv a x y - (y - Δ) ^ a := by unfold inv; linarith
  have hge : x ≤ solve a (inv a x y) (y - Δ) := by
    rcases hΔ.eq_or_lt with h | h
    · subst h; rw [sub_zero, solve_inv_self ha hx.le]
    · conv_lhs => rw [← solve_inv_self ha hx.le (y := y)]
      exact (solve_lt_solve ha (by linarith) (by linarith : y - Δ < y) (by
        unfold inv; linarith [rpow_nonneg hx.le a])).le
  refine ⟨by unfold inGivenOut; linarith, by unfold inGivenOut; linarith, by linarith, ?_⟩
  rw [inGivenOut, add_sub_cancel, inv_solve ha hk]

/-- Strictly positive input for a strictly positive output. -/
lemma inGivenOut_pos (ha : 0 < a) {x y Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hΔy : Δ < y) :
    0 < inGivenOut a x y Δ := by
  have hk : 0 ≤ inv a x y - (y - Δ) ^ a := by
    have : (y - Δ) ^ a ≤ y ^ a := rpow_le_rpow (by linarith) (by linarith) ha.le
    unfold inv; linarith [rpow_nonneg hx.le a]
  have := solve_lt_solve ha (k := inv a x y) (by linarith) (by linarith : y - Δ < y)
    (by unfold inv; linarith [rpow_nonneg hx.le a])
  rw [solve_inv_self ha hx.le] at this
  unfold inGivenOut; linarith

/-- **Theorem 4 (output-specified), uniqueness.** -/
theorem inGivenOut_unique (ha : 0 < a) {x y Δ d : ℝ} (hd : 0 ≤ x + d)
    (h : inv a (x + d) (y - Δ) = inv a x y) : d = inGivenOut a x y Δ := by
  have := eq_solve ha hd h
  unfold inGivenOut; linarith

/-! ### Theorem 6: path independence

Because the invariant is recomputed from the reserves, splitting a trade in the same
direction changes nothing. This holds for any fixed exponent, so it holds **with fees
too** (as the paper claims at the end of §5), as long as both legs go the same way. -/

/-- **Theorem 6 (input-specified).** -/
theorem outGivenIn_add (ha : 0 < a) {x y Δ₁ Δ₂ : ℝ} (hy : 0 ≤ y) (h₁ : 0 ≤ Δ₁) (h₂ : 0 ≤ Δ₂)
    (hv : (y + (Δ₁ + Δ₂)) ^ a ≤ inv a x y) :
    outGivenIn a x y (Δ₁ + Δ₂) =
      outGivenIn a x y Δ₁ + outGivenIn a (x - outGivenIn a x y Δ₁) (y + Δ₁) Δ₂ := by
  have hk : 0 ≤ inv a x y - (y + Δ₁) ^ a := by
    have : (y + Δ₁) ^ a ≤ (y + (Δ₁ + Δ₂)) ^ a := rpow_le_rpow (by linarith) (by linarith) ha.le
    linarith
  have hx1 : x - outGivenIn a x y Δ₁ = solve a (inv a x y) (y + Δ₁) := by
    unfold outGivenIn; ring
  rw [hx1]
  unfold outGivenIn
  rw [inv_solve ha hk, add_assoc]
  ring

/-- **Theorem 6 (output-specified).** -/
theorem inGivenOut_add (ha : 0 < a) {x y Δ₁ Δ₂ : ℝ} (hx : 0 ≤ x) (h₁ : 0 ≤ Δ₁) (hy : Δ₁ ≤ y) :
    inGivenOut a x y (Δ₁ + Δ₂) =
      inGivenOut a x y Δ₁ + inGivenOut a (x + inGivenOut a x y Δ₁) (y - Δ₁) Δ₂ := by
  have hk : 0 ≤ inv a x y - (y - Δ₁) ^ a := by
    have : (y - Δ₁) ^ a ≤ y ^ a := rpow_le_rpow (by linarith) (by linarith) ha.le
    unfold inv; linarith [rpow_nonneg hx a]
  have hx1 : x + inGivenOut a x y Δ₁ = solve a (inv a x y) (y - Δ₁) := by
    unfold inGivenOut; ring
  rw [hx1]
  unfold inGivenOut
  rw [inv_solve ha hk, sub_sub]
  ring

/-! ### Theorem 8: scale invariance

Scaling both reserves by `λ > 0` scales `k` by `λ ^ a` (`λ ^ (1 - t)`), **not** by `λ`.
Trade outputs are homogeneous of degree 1: scaling the reserves *and the trade size* by
`λ` scales the output by `λ`. Price and rate do not change. -/

theorem inv_smul {l x y : ℝ} (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    inv a (l * x) (l * y) = l ^ a * inv a x y := by
  simp [inv, mul_rpow hl hx, mul_rpow hl hy, mul_add]

lemma solve_smul (ha : 0 < a) {l k z : ℝ} (hl : 0 ≤ l) (hz : 0 ≤ z) (h : 0 ≤ k - z ^ a) :
    solve a (l ^ a * k) (l * z) = l * solve a k z := by
  unfold solve
  rw [mul_rpow hl hz, ← mul_sub, mul_rpow (rpow_nonneg hl _) h, rpow_rpow_inv hl ha.ne']

/-- **Theorem 8 (input-specified).** -/
theorem outGivenIn_smul (ha : 0 < a) {l x y Δ : ℝ} (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hΔ : 0 ≤ Δ) (hv : (y + Δ) ^ a ≤ inv a x y) :
    outGivenIn a (l * x) (l * y) (l * Δ) = l * outGivenIn a x y Δ := by
  unfold outGivenIn
  rw [inv_smul hl hx hy, ← mul_add, solve_smul ha hl (by linarith) (by linarith)]
  ring

/-- **Theorem 8 (output-specified).** -/
theorem inGivenOut_smul (ha : 0 < a) {l x y Δ : ℝ} (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hΔ : 0 ≤ Δ) (hΔy : Δ ≤ y) :
    inGivenOut a (l * x) (l * y) (l * Δ) = l * inGivenOut a x y Δ := by
  have hk : 0 ≤ inv a x y - (y - Δ) ^ a := by
    have : (y - Δ) ^ a ≤ y ^ a := rpow_le_rpow (by linarith) (by linarith) ha.le
    unfold inv; linarith [rpow_nonneg hx a]
  unfold inGivenOut
  rw [inv_smul hl hx hy, ← mul_sub, solve_smul ha hl (by linarith) hk]
  ring

/-- **Theorem 8 (price and rate).** -/
theorem price_smul {t l x y : ℝ} (hl : l ≠ 0) : price t (l * x) (l * y) = price t x y := by
  simp [price, mul_div_mul_left _ _ hl]

theorem rate_smul {t l x y : ℝ} (hl : l ≠ 0) : rate t (l * x) (l * y) = rate t x y := by
  simp [rate, mul_div_mul_left _ _ hl]

end YieldSpace
