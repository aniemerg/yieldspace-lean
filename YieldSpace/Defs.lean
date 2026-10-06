import Mathlib

/-!
# YieldSpace: definitions

Reference: Niemerg, Robinson, Livnev, *YieldSpace: An Automated Liquidity Provider for
Fixed Yield Tokens* (Aug 2020, working draft rev. 1).

Throughout, `x` is the base (Dai) reserve and `y` is the fyToken reserve (including any
virtual reserves, §6.3 of the paper). The invariant is the constant power sum
`x ^ (1 - t) + y ^ (1 - t) = k` (paper eq. 1).

All trade math is done for a *generic exponent* `a ∈ (0, 1)` standing for `1 - τ`, so the
same lemmas cover the fee-free curve (`τ = t`) and both fee curves of §5
(`τ = g * t` when buying fyToken, `τ = t / g` when selling fyToken).

The invariant is recomputed from the current reserves before every trade (paper §4.1),
so a trade is a pure function of `(a, x, y, Δ)`.
-/

noncomputable section

namespace YieldSpace

open Real

/-- The constant power sum `x ^ a + y ^ a` (paper eq. 1, with `a = 1 - t`). -/
def inv (a x y : ℝ) : ℝ := x ^ a + y ^ a

/-- Solve the invariant for one reserve: the `r ≥ 0` with `r ^ a + z ^ a = k`. -/
def solve (a k z : ℝ) : ℝ := (k - z ^ a) ^ a⁻¹

/-! ### Generic trades

The pool holds `x` of token X and `y` of token Y. -/

/-- Trader sends `Δ` of Y in; this much X comes out. -/
def outGivenIn (a x y Δ : ℝ) : ℝ := x - solve a (inv a x y) (y + Δ)

/-- Trader takes `Δ` of Y out; this much X must go in. -/
def inGivenOut (a x y Δ : ℝ) : ℝ := solve a (inv a x y) (y - Δ) - x

/-! ### Price and rate -/

/-- Marginal price of fyToken in base, `(x / y) ^ t` (reciprocal of paper eq. 13). -/
def price (t x y : ℝ) : ℝ := (x / y) ^ t

/-- Implied rate to maturity, `(y / x) ^ t - 1` (= `1 / price - 1`). -/
def rate (t x y : ℝ) : ℝ := (y / x) ^ t - 1

/-- The paper's interest rate `y / x - 1` (eqs. 2, 11): the rate per unit of scaled time. -/
def paperRate (x y : ℝ) : ℝ := y / x - 1

/-! ### Fees (paper §5) -/

/-- Time to maturity `t` and fee parameter `g` (`g = 1` means no fee). The paper needs
`t / g < 1` so that the sell-side exponent `1 - t / g` stays positive (footnote 4). -/
structure Params where
  t : ℝ
  g : ℝ
  t_pos : 0 < t
  g_pos : 0 < g
  g_le_one : g ≤ 1
  t_lt_g : t < g

namespace Params

variable (p : Params)

/-- Exponent used when the trader buys fyToken: `1 - g t` (paper eq. 20). -/
def aBuy : ℝ := 1 - p.g * p.t

/-- Exponent used when the trader sells fyToken: `1 - t / g` (paper eq. 20, footnote). -/
def aSell : ℝ := 1 - p.t / p.g

/-- Sell `Δ` fyToken, receive base. -/
def sellFYToken (x y Δ : ℝ) : ℝ := outGivenIn p.aSell x y Δ

/-- Buy `Δ` fyToken, pay base. -/
def buyFYToken (x y Δ : ℝ) : ℝ := inGivenOut p.aBuy x y Δ

/-- Sell `Δ` base, receive fyToken (a fyToken buy, so it uses `aBuy`). -/
def sellBase (x y Δ : ℝ) : ℝ := outGivenIn p.aBuy y x Δ

/-- Buy `Δ` base, pay fyToken (a fyToken sell, so it uses `aSell`). -/
def buyBase (x y Δ : ℝ) : ℝ := inGivenOut p.aSell y x Δ

/-- The fee-free parameters for time `t`. -/
def noFee (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : Params :=
  ⟨t, 1, h0, one_pos, le_rfl, h1⟩

end Params

end YieldSpace
