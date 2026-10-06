import YieldSpace.Trades

/-!
# Fee exponents, monotonicity (Thm 2), and round trips (Thm 3)
-/

namespace YieldSpace

open Real

/-! ### Bounds on the fee exponents -/

namespace Params

variable (p : Params)

lemma aSell_pos : 0 < p.aSell := by
  have : p.t / p.g < 1 := (div_lt_one p.g_pos).2 p.t_lt_g
  unfold aSell; linarith

lemma aSell_lt_one : p.aSell < 1 := by
  have : 0 < p.t / p.g := div_pos p.t_pos p.g_pos
  unfold aSell; linarith

lemma aBuy_pos : 0 < p.aBuy := by
  have : p.g * p.t ≤ p.t := mul_le_of_le_one_left p.t_pos.le p.g_le_one
  unfold aBuy; linarith [p.t_lt_g, p.g_le_one]

lemma aBuy_lt_one : p.aBuy < 1 := by
  have : 0 < p.g * p.t := mul_pos p.g_pos p.t_pos
  unfold aBuy; linarith

lemma aSell_le_aBuy : p.aSell ≤ p.aBuy := by
  have h1 : p.g * p.t ≤ p.t := mul_le_of_le_one_left p.t_pos.le p.g_le_one
  have h2 : p.t ≤ p.t / p.g := le_div_self p.t_pos.le p.g_pos p.g_le_one
  unfold aSell aBuy; linarith

/-- With a real fee (`g < 1`) the selling curve is strictly flatter in the exponent. -/
lemma aSell_lt_aBuy (hg : p.g < 1) : p.aSell < p.aBuy := by
  have h1 : p.g * p.t < p.t := mul_lt_of_lt_one_left p.t_pos hg
  have h2 : p.t ≤ p.t / p.g := le_div_self p.t_pos.le p.g_pos p.g_le_one
  unfold aSell aBuy; linarith

lemma noFee_aSell {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : (noFee t h0 h1).aSell = 1 - t := by
  simp [noFee, aSell]

lemma noFee_aBuy {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : (noFee t h0 h1).aBuy = 1 - t := by
  simp [noFee, aBuy]

end Params

/-! ### Theorem 2: monotonicity -/

lemma price_lt_price {t x y x' y' : ℝ} (ht : 0 < t) (hx : 0 < x) (hy' : 0 < y')
    (hxx : x ≤ x') (hyy : y' < y) : price t x y < price t x' y' := by
  have hy : 0 < y := hy'.trans hyy
  have : x / y < x' / y' := by
    rw [div_lt_div_iff₀ hy hy']; nlinarith
  exact rpow_lt_rpow (div_nonneg hx.le hy.le) this ht

variable {a : ℝ}

/-- **Theorem 2.** Buying `Δ > 0` fyToken (output-specified) strictly raises its price. -/
theorem price_lt_after_buyFY (ha : 0 < a) {t x y Δ : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hΔ : 0 < Δ) (hΔy : Δ < y) :
    price t x y < price t (x + inGivenOut a x y Δ) (y - Δ) :=
  price_lt_price ht hx (by linarith) (by linarith [(inGivenOut_spec ha hx hΔ.le hΔy).1])
    (by linarith)

/-- **Theorem 2.** Buying fyToken by selling `Δ > 0` base (input-specified) strictly raises
the fyToken price. -/
theorem price_lt_after_sellBase (ha : 0 < a) {t x y Δ : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hy : 0 < y) (hΔ : 0 < Δ) (hv : Valid a y x Δ) :
    price t x y < price t (x + Δ) (y - outGivenIn a y x Δ) :=
  price_lt_price ht hx (outGivenIn_spec ha hy hx.le hΔ.le hv).2.1 (by linarith)
    (by linarith [outGivenIn_pos ha hy hx.le hΔ hv])

/-- **Theorem 2.** Selling `Δ > 0` fyToken (input-specified) strictly lowers its price. -/
theorem price_after_sellFY_lt (ha : 0 < a) {t x y Δ : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hy : 0 < y) (hΔ : 0 < Δ) (hv : Valid a x y Δ) :
    price t (x - outGivenIn a x y Δ) (y + Δ) < price t x y :=
  price_lt_price ht (outGivenIn_spec ha hx hy.le hΔ.le hv).2.1 hy
    (by linarith [outGivenIn_pos ha hx hy.le hΔ hv]) (by linarith)

/-- **Theorem 2.** Selling fyToken to take `Δ > 0` base out (output-specified) strictly
lowers the fyToken price. -/
theorem price_after_buyBase_lt (ha : 0 < a) {t x y Δ : ℝ} (ht : 0 < t) (hy : 0 < y)
    (hΔ : 0 < Δ) (hΔx : Δ < x) :
    price t (x - Δ) (y + inGivenOut a y x Δ) < price t x y :=
  price_lt_price ht (by linarith) hy (by linarith)
    (by linarith [inGivenOut_pos ha hy hΔ hΔx])

/-! ### Theorem 3: round trips -/

/-- Selling `Δ` along the curve leaves this much X in the pool. -/
lemma sub_outGivenIn (x y Δ : ℝ) : x - outGivenIn a x y Δ = solve a (inv a x y) (y + Δ) := by
  unfold outGivenIn; ring

/-- **Theorem 3 (no fee).** Selling `Δ` Y and buying `Δ` Y back on the same curve is
exactly break-even. -/
theorem roundTrip_eq (ha : 0 < a) {x y Δ : ℝ} (hx : 0 ≤ x) (hk : (y + Δ) ^ a ≤ inv a x y) :
    inGivenOut a (x - outGivenIn a x y Δ) (y + Δ) Δ = outGivenIn a x y Δ := by
  rw [sub_outGivenIn]
  unfold inGivenOut
  rw [inv_solve ha (by linarith), add_sub_cancel_right, solve_inv_self ha hx]
  unfold outGivenIn; ring

/-- Same-length increments of a strictly convex function grow strictly when the interval
moves right (here `v ≤ w`, so the intervals do not overlap). -/
lemma increment_lt {φ : ℝ → ℝ} (hφ : StrictConvexOn ℝ (Set.Ici 0) φ) {u v w w' : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvw : v ≤ w) (hlen : w' - w = v - u) :
    φ v - φ u < φ w' - φ w := by
  have hd : 0 < v - u := by linarith
  have hmem : ∀ {z}, u ≤ z → z ∈ Set.Ici (0 : ℝ) := fun h => Set.mem_Ici.2 (hu.trans h)
  have key : (φ v - φ u) / (v - u) < (φ w' - φ w) / (w' - w) := by
    rcases hvw.eq_or_lt with h | h
    · subst h
      exact hφ.slope_strict_mono_adjacent (hmem le_rfl) (hmem (by linarith)) huv (by linarith)
    · calc (φ v - φ u) / (v - u) < (φ w - φ v) / (w - v) :=
            hφ.slope_strict_mono_adjacent (hmem le_rfl) (hmem (by linarith)) huv h
        _ < (φ w' - φ w) / (w' - w) :=
            hφ.slope_strict_mono_adjacent (hmem huv.le) (hmem (by linarith)) h (by linarith)
  rw [hlen] at key
  exact (div_lt_div_iff_of_pos_right hd).1 key

/-- **Theorem 3 (core).** Sell `Δ` Y on the flatter curve `α`, then buy `Δ` back on the
steeper curve `β > α`: the buy-back costs strictly more X than the sale paid, **provided
`x ≤ y`** (non-negative rates). Without that hypothesis the claim is false; see README. -/
theorem roundTrip_lt {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {x y Δ : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hΔ : 0 < Δ) (hv : Valid α x y Δ) :
    outGivenIn α x y Δ < inGivenOut β (x - outGivenIn α x y Δ) (y + Δ) Δ := by
  have hβ : 0 < β := hα.trans hαβ
  have hy : 0 < y := hx.trans_le hxy
  obtain ⟨-, hx1pos, hinv⟩ := outGivenIn_spec hα hx hy.le hΔ.le hv
  set x1 := x - outGivenIn α x y Δ with hx1def
  have hx1lt : x1 < x := by linarith [outGivenIn_pos hα hx hy.le hΔ hv]
  -- move to `α`-power coordinates and use convexity of `z ↦ z ^ (β / α)`
  have hconv : StrictConvexOn ℝ (Set.Ici 0) (fun z : ℝ => z ^ (β / α)) :=
    strictConvexOn_rpow ((one_lt_div hα).2 hαβ)
  have hpow : ∀ {z : ℝ}, 0 ≤ z → (z ^ α) ^ (β / α) = z ^ β := by
    intro z hz
    rw [← rpow_mul hz, mul_div_cancel₀ _ hα.ne']
  have hlen : (y + Δ) ^ α - y ^ α = x ^ α - x1 ^ α := by
    unfold inv at hinv; linarith
  have hinc := increment_lt hconv (rpow_nonneg hx1pos.le α)
    (rpow_lt_rpow hx1pos.le hx1lt hα) (rpow_le_rpow hx.le hxy hα.le) hlen
  simp only [hpow hx.le, hpow hx1pos.le, hpow hy.le, hpow (by linarith : (0 : ℝ) ≤ y + Δ)]
    at hinc
  -- `x` is strictly below the X-reserve that the buy-back curve requires
  have hlt : x < solve β (inv β x1 (y + Δ)) y := by
    have h0 : 0 ≤ x ^ β := rpow_nonneg hx.le β
    have : x ^ β < inv β x1 (y + Δ) - y ^ β := by unfold inv; linarith
    have := rpow_lt_rpow h0 this (inv_pos.2 hβ)
    rwa [rpow_rpow_inv hx.le hβ.ne'] at this
  unfold inGivenOut
  rw [add_sub_cancel_right]
  have : outGivenIn α x y Δ = x - x1 := by rw [hx1def]; ring
  linarith

/-- **Theorem 3 (fees, fyToken round trip).** Sell `Δ` fyToken, then buy `Δ` fyToken
back: with a real fee (`g < 1`) and `x ≤ y`, the trader strictly loses base. -/
theorem Params.roundTrip_loss (p : Params) (hg : p.g < 1) {x y Δ : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hΔ : 0 < Δ) (hv : Valid p.aSell x y Δ) :
    p.sellFYToken x y Δ < p.buyFYToken (x - p.sellFYToken x y Δ) (y + Δ) Δ :=
  roundTrip_lt p.aSell_pos (p.aSell_lt_aBuy hg) hx hxy hΔ hv

/-- **Theorem 3 (no fee, fyToken round trip).** Break-even. -/
theorem Params.roundTrip_noFee {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {x y Δ : ℝ} (hx : 0 ≤ x)
    (hk : (y + Δ) ^ (1 - t) ≤ inv (1 - t) x y) :
    (noFee t h0 h1).buyFYToken (x - (noFee t h0 h1).sellFYToken x y Δ) (y + Δ) Δ =
      (noFee t h0 h1).sellFYToken x y Δ := by
  simp only [Params.buyFYToken, Params.sellFYToken, Params.noFee_aSell, Params.noFee_aBuy]
  exact roundTrip_eq (by linarith) hx hk

end YieldSpace
