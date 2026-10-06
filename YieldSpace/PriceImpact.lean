import YieldSpace.Monotone

/-!
# Theorem 7: price impact

For a trade on the curve with exponent `a = 1 - τ`, the marginal price of Y in X is
`(x / y) ^ τ`. The average execution price lies strictly between the pre-trade and
post-trade marginal prices, so it gets strictly worse as the trade gets bigger.

Proof idea: in `a`-power coordinates `u = x ^ a`, `w = y ^ a` the invariant is linear
(`u + w = k`), so a trade moves `u` and `w` by the same amount `d`. Real reserves are
`ψ u`, `ψ w` with `ψ z = z ^ (1/a)`. The mean value theorem gives
`out = ψ' ξ * d`, `Δ = ψ' η * d`, so `out / Δ = (ξ / η) ^ (1/a - 1)` for some `ξ`, `η`
inside the two intervals.
-/

namespace YieldSpace

open Real Set

variable {a : ℝ}

lemma mvt_rpow {p u v : ℝ} (hp : 0 ≤ p) (hu : 0 < u) (huv : u < v) :
    ∃ ξ ∈ Ioo u v, v ^ p - u ^ p = p * ξ ^ (p - 1) * (v - u) := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun z : ℝ => z ^ p)
    (fun z => p * z ^ (p - 1)) huv
    (fun z _ => (continuousAt_rpow_const z p (Or.inr hp)).continuousWithinAt)
    (fun z hz => hasDerivAt_rpow_const (Or.inl (hu.trans hz.1).ne'))
  refine ⟨ξ, hξ, ?_⟩
  rw [h, div_mul_cancel₀ _ (sub_pos.2 huv).ne']

lemma div_lt_div_of_lt_of_lt {A A' B B' : ℝ} (hA : 0 ≤ A) (hAA : A < A') (hB' : 0 < B')
    (hBB : B' < B) : A / B < A' / B' := by
  rw [div_lt_div_iff₀ (hB'.trans hBB) hB']
  nlinarith

/-- **Theorem 7 (selling Y, input-specified).**
`post price < average price < pre price`. -/
theorem avgPrice_outGivenIn (ha0 : 0 < a) (ha1 : a < 1) {x y Δ : ℝ} (hx : 0 < x)
    (hy : 0 < y) (hΔ : 0 < Δ) (hv : Valid a x y Δ) :
    ((x - outGivenIn a x y Δ) / (y + Δ)) ^ (1 - a) < outGivenIn a x y Δ / Δ ∧
      outGivenIn a x y Δ / Δ < (x / y) ^ (1 - a) := by
  obtain ⟨-, hx1pos, hinv⟩ := outGivenIn_spec ha0 hx hy.le hΔ.le hv
  have hout := outGivenIn_pos ha0 hx hy.le hΔ hv
  set x1 := x - outGivenIn a x y Δ with hx1def
  have hx1lt : x1 < x := by linarith
  have hyΔ : 0 < y + Δ := by linarith
  set p := a⁻¹
  set c := p - 1
  have hp : 1 < p := one_lt_inv_iff₀.2 ⟨ha0, ha1⟩
  have hc : 0 < c := by simp only [c]; linarith
  -- coordinates
  have hψ : ∀ {z : ℝ}, 0 ≤ z → (z ^ a) ^ p = z := fun hz => rpow_rpow_inv hz ha0.ne'
  have hφ : ∀ {z : ℝ}, 0 ≤ z → (z ^ a) ^ c = z ^ (1 - a) := by
    intro z hz
    rw [← rpow_mul hz]; congr 1; simp only [c, p]; field_simp
  have hlen : (y + Δ) ^ a - y ^ a = x ^ a - x1 ^ a := by unfold inv at hinv; linarith
  have hd : 0 < x ^ a - x1 ^ a := by linarith [rpow_lt_rpow hx1pos.le hx1lt ha0]
  obtain ⟨ξ, ⟨hξ1, hξ2⟩, hξ⟩ :=
    mvt_rpow (by linarith : (0 : ℝ) ≤ p) (rpow_pos_of_pos hx1pos a)
      (rpow_lt_rpow hx1pos.le hx1lt ha0)
  obtain ⟨η, ⟨hη1, hη2⟩, hη⟩ :=
    mvt_rpow (by linarith : (0 : ℝ) ≤ p) (rpow_pos_of_pos hy a)
      (rpow_lt_rpow hy.le (by linarith : y < y + Δ) ha0)
  rw [hψ hx.le, hψ hx1pos.le] at hξ
  rw [hψ hy.le, hψ hyΔ.le, hlen] at hη
  have hξ0 : 0 < ξ := (rpow_pos_of_pos hx1pos a).trans hξ1
  have hη0 : 0 < η := (rpow_pos_of_pos hy a).trans hη1
  have hppos : 0 < p := by linarith
  -- `out / Δ = ξ ^ c / η ^ c`
  have hratio : outGivenIn a x y Δ / Δ = ξ ^ c / η ^ c := by
    have h1 : outGivenIn a x y Δ = p * ξ ^ c * (x ^ a - x1 ^ a) := by rw [← hξ]; ring
    have h2 : Δ = p * η ^ c * (x ^ a - x1 ^ a) := by rw [← hη]; ring
    rw [h1, h2]
    field_simp
  rw [hratio]
  constructor
  · rw [div_rpow hx1pos.le hyΔ.le, ← hφ hx1pos.le, ← hφ hyΔ.le]
    exact div_lt_div_of_lt_of_lt (rpow_nonneg (rpow_nonneg hx1pos.le a) c)
      (rpow_lt_rpow (rpow_nonneg hx1pos.le a) hξ1 hc) (rpow_pos_of_pos hη0 c)
      (rpow_lt_rpow hη0.le hη2 hc)
  · rw [div_rpow hx.le hy.le, ← hφ hx.le, ← hφ hy.le]
    exact div_lt_div_of_lt_of_lt (rpow_nonneg hξ0.le c) (rpow_lt_rpow hξ0.le hξ2 hc)
      (rpow_pos_of_pos (rpow_pos_of_pos hy a) c)
      (rpow_lt_rpow (rpow_nonneg hy.le a) hη1 hc)

/-- Reversing an output-specified trade with an input-specified one returns the input. -/
lemma outGivenIn_reverse (ha : 0 < a) {x y Δ : ℝ} (hx : 0 < x) (hΔ : 0 ≤ Δ) (hΔy : Δ < y) :
    outGivenIn a (x + inGivenOut a x y Δ) (y - Δ) Δ = inGivenOut a x y Δ := by
  have hinv := (inGivenOut_spec ha hx hΔ hΔy).2.2.2
  unfold outGivenIn
  rw [hinv, sub_add_cancel, solve_inv_self ha hx.le]
  ring

/-- **Theorem 7 (buying Y, output-specified).**
`pre price < average price < post price`. -/
theorem avgPrice_inGivenOut (ha0 : 0 < a) (ha1 : a < 1) {x y Δ : ℝ} (hx : 0 < x)
    (hΔ : 0 < Δ) (hΔy : Δ < y) :
    (x / y) ^ (1 - a) < inGivenOut a x y Δ / Δ ∧
      inGivenOut a x y Δ / Δ < ((x + inGivenOut a x y Δ) / (y - Δ)) ^ (1 - a) := by
  obtain ⟨-, hx'pos, hy'pos, hinv⟩ := inGivenOut_spec ha0 hx hΔ.le hΔy
  have hv : Valid a (x + inGivenOut a x y Δ) (y - Δ) Δ := by
    unfold Valid; rw [hinv, sub_add_cancel]; unfold inv
    linarith [rpow_pos_of_pos hx a]
  have h := avgPrice_outGivenIn ha0 ha1 hx'pos hy'pos hΔ hv
  rw [outGivenIn_reverse ha0 hx hΔ.le hΔy, add_sub_cancel_right, sub_add_cancel] at h
  exact h

/-- **Theorem 7, consequence.** Larger sells get strictly worse average prices. -/
theorem avgPrice_outGivenIn_strictAnti (ha0 : 0 < a) (ha1 : a < 1) {x y Δ₁ Δ₂ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h₁ : 0 < Δ₁) (h₁₂ : Δ₁ < Δ₂) (hv : Valid a x y Δ₂) :
    outGivenIn a x y Δ₂ / Δ₂ < outGivenIn a x y Δ₁ / Δ₁ := by
  have hv₁ : Valid a x y Δ₁ :=
    lt_of_le_of_lt (rpow_le_rpow (by linarith) (by linarith) ha0.le) hv
  obtain ⟨-, hx1pos, hinv⟩ := outGivenIn_spec ha0 hx hy.le h₁.le hv₁
  have hsplit := outGivenIn_add ha0 (Δ₁ := Δ₁) (Δ₂ := Δ₂ - Δ₁) hy.le h₁.le (by linarith)
    (by rw [add_sub_cancel]; exact hv.le)
  rw [add_sub_cancel] at hsplit
  have hv₂ : Valid a (x - outGivenIn a x y Δ₁) (y + Δ₁) (Δ₂ - Δ₁) := by
    unfold Valid; rw [hinv, add_add_sub_cancel]; exact hv
  have hlow := (avgPrice_outGivenIn ha0 ha1 hx hy h₁ hv₁).1
  have hhigh := (avgPrice_outGivenIn ha0 ha1 hx1pos (by linarith) (by linarith) hv₂).2
  set o₁ := outGivenIn a x y Δ₁
  set o₂ := outGivenIn a (x - o₁) (y + Δ₁) (Δ₂ - Δ₁)
  have key : o₂ / (Δ₂ - Δ₁) < o₁ / Δ₁ := hhigh.trans hlow
  rw [hsplit, div_lt_div_iff₀ (by linarith) h₁]
  rw [div_lt_div_iff₀ (by linarith) h₁] at key
  nlinarith

/-- **Theorem 7, consequence.** Larger buys get strictly worse average prices. -/
theorem avgPrice_inGivenOut_strictMono (ha0 : 0 < a) (ha1 : a < 1) {x y Δ₁ Δ₂ : ℝ}
    (hx : 0 < x) (h₁ : 0 < Δ₁) (h₁₂ : Δ₁ < Δ₂) (h₂ : Δ₂ < y) :
    inGivenOut a x y Δ₁ / Δ₁ < inGivenOut a x y Δ₂ / Δ₂ := by
  obtain ⟨-, hx1pos, -, -⟩ := inGivenOut_spec ha0 hx h₁.le (h₁₂.trans h₂)
  have hsplit := inGivenOut_add ha0 (y := y) (Δ₁ := Δ₁) (Δ₂ := Δ₂ - Δ₁) hx.le h₁.le
    (by linarith)
  rw [add_sub_cancel] at hsplit
  have hhigh := (avgPrice_inGivenOut ha0 ha1 (y := y) hx h₁ (by linarith)).2
  have hlow := (avgPrice_inGivenOut ha0 ha1 hx1pos (by linarith : 0 < Δ₂ - Δ₁)
    (by linarith : Δ₂ - Δ₁ < y - Δ₁)).1
  set i₁ := inGivenOut a x y Δ₁
  set i₂ := inGivenOut a (x + i₁) (y - Δ₁) (Δ₂ - Δ₁)
  have key : i₁ / Δ₁ < i₂ / (Δ₂ - Δ₁) := hhigh.trans hlow
  rw [hsplit, div_lt_div_iff₀ h₁ (by linarith)]
  rw [div_lt_div_iff₀ h₁ (by linarith)] at key
  nlinarith

/-! ### Fee-free statements in terms of `price t` -/

/-- **Theorem 7 (no fee, selling fyToken).** -/
theorem avgPrice_sellFY_noFee {t x y Δ : ℝ} (h0 : 0 < t) (h1 : t < 1) (hx : 0 < x)
    (hy : 0 < y) (hΔ : 0 < Δ) (hv : Valid (1 - t) x y Δ) :
    price t (x - outGivenIn (1 - t) x y Δ) (y + Δ) < outGivenIn (1 - t) x y Δ / Δ ∧
      outGivenIn (1 - t) x y Δ / Δ < price t x y := by
  have h := avgPrice_outGivenIn (by linarith) (by linarith) hx hy hΔ hv
  simp only [sub_sub_cancel] at h
  exact h

/-- **Theorem 7 (no fee, buying fyToken).** -/
theorem avgPrice_buyFY_noFee {t x y Δ : ℝ} (h0 : 0 < t) (h1 : t < 1) (hx : 0 < x)
    (hΔ : 0 < Δ) (hΔy : Δ < y) :
    price t x y < inGivenOut (1 - t) x y Δ / Δ ∧
      inGivenOut (1 - t) x y Δ / Δ < price t (x + inGivenOut (1 - t) x y Δ) (y - Δ) := by
  have h := avgPrice_inGivenOut (a := 1 - t) (by linarith) (by linarith) hx hΔ hΔy
  simp only [sub_sub_cancel] at h
  exact h

end YieldSpace
