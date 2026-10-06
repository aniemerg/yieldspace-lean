import YieldSpace.Monotone

/-!
# Theorem 5: convergence to constant sum at maturity

As `t → 0` every exponent in play (`1 - t`, `1 - g t`, `1 - t / g`) tends to `1`, and at
exponent `1` the invariant is `x + y = k`. We prove continuity in the exponent at `a = 1`,
for the curve itself and for both kinds of trade, then specialise to `t → 0`.

Hypotheses such as `Δ < x` are not needed for the limit itself (Lean's `rpow` is
continuous at exponent `1` for any base), but we keep them so that every statement is
about trades that make sense in the constant-sum limit.
-/

namespace YieldSpace

open Real Filter Topology

/-- The curve through `(x₀, y₀)`, solved for X at `Y = z`, is continuous in the exponent
at `a = 1`, where it equals the constant-sum value `x₀ + y₀ - z`. -/
theorem tendsto_solve_one (x₀ y₀ z : ℝ) :
    Tendsto (fun a => solve a (inv a x₀ y₀) z) (𝓝 1) (𝓝 (x₀ + y₀ - z)) := by
  have hc : ∀ b : ℝ, ContinuousAt (fun a : ℝ => b ^ a) 1 := fun b =>
    continuousAt_const.rpow continuousAt_id (Or.inr one_pos)
  have hcont : ContinuousAt (fun a => solve a (inv a x₀ y₀) z) 1 := by
    unfold solve inv
    exact (((hc x₀).add (hc y₀)).sub (hc z)).rpow (continuousAt_id.inv₀ one_ne_zero)
      (Or.inr (by simp))
  simpa [solve, inv] using hcont.tendsto

/-- **Theorem 5 (curve).** Along any exponent path `e t → 1`, the curve converges
pointwise to the constant-sum line `x + y = x₀ + y₀`. -/
theorem tendsto_curve {ι : Type*} {l : Filter ι} {e : ι → ℝ} (he : Tendsto e l (𝓝 1))
    (x₀ y₀ z : ℝ) :
    Tendsto (fun i => solve (e i) (inv (e i) x₀ y₀) z) l (𝓝 (x₀ + y₀ - z)) :=
  (tendsto_solve_one x₀ y₀ z).comp he

/-- **Theorem 5 (selling Y).** The output tends to `Δ`: a 1:1 exchange. -/
theorem tendsto_outGivenIn {ι : Type*} {l : Filter ι} {e : ι → ℝ} (he : Tendsto e l (𝓝 1))
    (x y Δ : ℝ) : Tendsto (fun i => outGivenIn (e i) x y Δ) l (𝓝 Δ) := by
  convert (tendsto_curve he x y (y + Δ)).const_sub x using 2 <;> first | rfl | ring

/-- **Theorem 5 (buying Y).** The required input tends to `Δ`. -/
theorem tendsto_inGivenOut {ι : Type*} {l : Filter ι} {e : ι → ℝ} (he : Tendsto e l (𝓝 1))
    (x y Δ : ℝ) : Tendsto (fun i => inGivenOut (e i) x y Δ) l (𝓝 Δ) := by
  convert (tendsto_curve he x y (y - Δ)).sub_const x using 2 <;> first | rfl | ring

/-! ### Specialisations to `t → 0` -/

lemma tendsto_one_sub : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun t : ℝ => 1 - t) := by fun_prop
  simpa using hc.tendsto (0 : ℝ)

lemma tendsto_one_sub_mul (g : ℝ) : Tendsto (fun t : ℝ => 1 - g * t) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun t : ℝ => 1 - g * t) := by fun_prop
  simpa using hc.tendsto (0 : ℝ)

lemma tendsto_one_sub_div (g : ℝ) : Tendsto (fun t : ℝ => 1 - t / g) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun t : ℝ => 1 - t / g) := by fun_prop
  simpa using hc.tendsto (0 : ℝ)

/-- **Theorem 5 (fee-free).** Selling `Δ` fyToken yields `→ Δ` base as `t → 0`. -/
theorem tendsto_sellFY_noFee (x y Δ : ℝ) :
    Tendsto (fun t => outGivenIn (1 - t) x y Δ) (𝓝 0) (𝓝 Δ) :=
  tendsto_outGivenIn tendsto_one_sub x y Δ

/-- **Theorem 5 (with fees).** For a fixed fee parameter `g`, all four fee trades become
1:1 as `t → 0`. -/
theorem tendsto_feeTrades (g x y Δ : ℝ) :
    Tendsto (fun t => outGivenIn (1 - t / g) x y Δ) (𝓝 0) (𝓝 Δ) ∧
    Tendsto (fun t => inGivenOut (1 - g * t) x y Δ) (𝓝 0) (𝓝 Δ) ∧
    Tendsto (fun t => outGivenIn (1 - g * t) y x Δ) (𝓝 0) (𝓝 Δ) ∧
    Tendsto (fun t => inGivenOut (1 - t / g) y x Δ) (𝓝 0) (𝓝 Δ) :=
  ⟨tendsto_outGivenIn (tendsto_one_sub_div g) x y Δ,
   tendsto_inGivenOut (tendsto_one_sub_mul g) x y Δ,
   tendsto_outGivenIn (tendsto_one_sub_mul g) y x Δ,
   tendsto_inGivenOut (tendsto_one_sub_div g) y x Δ⟩

/-- **Theorem 5 (price).** The marginal price tends to `1` as `t → 0`. -/
theorem tendsto_price {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun t => price t x y) (𝓝 0) (𝓝 1) := by
  have : ContinuousAt (fun t : ℝ => (x / y) ^ t) 0 :=
    continuousAt_const.rpow continuousAt_id (Or.inl (div_pos hx hy).ne')
  simpa [price] using this.tendsto

end YieldSpace
