# YieldSpace in Lean 4

A Lean 4 + Mathlib formalization of the trading math in *YieldSpace: An Automated Liquidity
Provider for Fixed Yield Tokens* (Niemerg, Robinson, Livnev, Aug 2020,
https://yield.is/YieldSpace.pdf).

```
lake exe cache get && lake build        # builds everything
lake env lean AxiomCheck.lean           # every headline theorem: [propext, Classical.choice, Quot.sound]
```

There are no `sorry`s.

## Model

| Paper | Lean (`YieldSpace/Defs.lean`) |
|---|---|
| `x^(1-t) + y^(1-t) = k` | `inv a x y = x^a + y^a`, with `a = 1 - τ` |
| solve the invariant for the other reserve | `solve a k z = (k - z^a)^(1/a)` |
| trade with input given / output given | `outGivenIn a x y Δ`, `inGivenOut a x y Δ` |
| fyToken price `(x/y)^t` | `price t x y` |
| rate | `rate t x y = (y/x)^t - 1` and `paperRate x y = y/x - 1` |
| fees (§5): `1 - g t` for fyToken buys, `1 - t/g` for fyToken sells | `Params.aBuy`, `Params.aSell`, `sellFYToken`, `buyFYToken`, `sellBase`, `buyBase` |

Every trade lemma is proved for a generic exponent `a ∈ (0,1)`. That one proof covers the
fee-free curve and both fee curves.

## Theorems

| # | Statement | Where |
|---|---|---|
| 1 | `x ≤ y → price ≤ 1`, and both rates are `≥ 0` | `Rates.lean` `price_le_one`, `rate_nonneg`, `paperRate_nonneg` |
| 2 | buys strictly raise the price, sells strictly lower it (all 4 trade types) | `Monotone.lean` `price_lt_after_buyFY`, `price_lt_after_sellBase`, `price_after_sellFY_lt`, `price_after_buyBase_lt` |
| 3 | round trip: break-even with no fee; strict loss with a fee **when `x ≤ y`** | `Monotone.lean` `roundTrip_eq`, `roundTrip_lt`, `Params.roundTrip_noFee`, `Params.roundTrip_loss` |
| 4 | existence, uniqueness, positivity of reserves, invariant preserved | `Trades.lean` `outGivenIn_spec/unique`, `inGivenOut_spec/unique`, `valid_of_le` |
| 5 | as `t → 0`: the curve converges pointwise to `x + y = k`, every trade (with or without fees) becomes 1:1, and the price goes to 1 | `Maturity.lean` `tendsto_curve`, `tendsto_feeTrades`, `tendsto_sellFY_noFee`, `tendsto_price` |
| 6 | path independence; also holds **with fees**, for same-direction trades | `Trades.lean` `outGivenIn_add`, `inGivenOut_add` |
| 7 | the average price lies strictly between the pre- and post-trade marginal prices, and it gets strictly worse as the trade grows | `PriceImpact.lean` `avgPrice_outGivenIn`, `avgPrice_inGivenOut`, `…_strictAnti`, `…_strictMono`, `avgPrice_*_noFee` |
| 8 | `k ↦ λ^(1-t) k`; scaling the reserves *and the trade size* by `λ` scales the output by `λ`; price and rate are unchanged | `Trades.lean` `inv_smul`, `outGivenIn_smul`, `inGivenOut_smul`, `price_smul`, `rate_smul` |

## Precise statements, where they differ from the informal request

* **Thm 3 (with fees)** needs `x ≤ y`, i.e. a non-negative rate. Without it the claim is
  **false**. Example: `t = 0.5`, `g = 0.95`, `x = 200`, `y = 100`. Selling 10 fyToken
  yields 13.78 base, and buying the 10 back costs only 13.35. The trader profits 0.43.
  The paper hints at this in footnote 6 and Appendix E: when rates are negative, the fee
  benefits the trader. A strict loss also needs a real fee, `g < 1`. The core lemma
  only needs the post-sale base reserve to stay below `y`, which is weaker than `x ≤ y`.
* **Thm 4.** For an output-specified trade, `0 ≤ Δ < (reserve being withdrawn)` is the exact
  condition. For an input-specified trade the exact domain is `(y+Δ)^a < k`, because
  the power-sum curve hits the axis at `y = k^(1/a)`, unlike `xy = k`. The sufficient
  condition `Δ ≤ x` (input at most the *opposite* reserve) is proved to imply it.
  "Exactly one output" means unique among outputs that leave a non-negative reserve.
* **Thm 7 with fees.** The bracketing marginal price is the trade's own curve price,
  `(x/y)^(gt)` or `(x/y)^(t/g)`. The fee-free corollaries are stated with `price t`.
* **Thm 8.** The output is homogeneous of degree 1 when the trade size is scaled as well.
  Under pure reserve scaling with a fixed trade size there is no clean power law.
* **Thm 5.** The convergence is pointwise for each fixed reserve and trade size. It is
  not proved to be uniform.

## Paper vs. request vs. formalization

1. **Rate.** The paper's rate is `r = y/x - 1` (eqs. 2, 11). That is the rate per unit of
   scaled time (`t = 1` is four years in fyDai). The request's `(y/x)^t - 1` is the
   compounded rate to maturity. Both are defined, and `one_add_rate` proves
   `1 + rate = (1 + paperRate)^t`.
2. **Price direction.** The paper's `p = (y/x)^t` (eq. 13) is the price of *Dai in fyDai*.
   The request's `(x/y)^t` is its reciprocal, the fyToken price in base. The two are
   consistent.
3. **Range of `t`.** The paper allows `0 ≤ t < 1`, and with fees it needs `t/g < 1`
   (footnote 4). `Params` encodes `0 < t < g ≤ 1`. The strict monotonicity results need
   `t > 0`.
4. **The §6.3 worked example does not use the fee.** Selling 100 fyDai into (100 Dai,
   100 virtual fyDai) at `t = 0.5` gives 65.69 Dai only with exponent `1 - t` (65.685).
   The text says the sell invariant uses `1 - t/g` with `g = 0.95`, which gives 64.61.
5. **The paper defines fees by trade direction only.** It says "buying" vs "selling"
   fyDai. It does not say how input-specified and output-specified trades map onto the
   curves. Here, every fyToken buy (`buyFYToken`, `sellBase`) uses `1 - gt` and every
   fyToken sell (`sellFYToken`, `buyBase`) uses `1 - t/g`.
6. **Path independence with fees.** The paper's end-of-§5 claim is right, and is proved
   here, for trades in the *same* direction only. Mixed directions are exactly the
   round-trip case.
7. **Not formalized:** liquidity tokens, the virtual-reserve accounting, and the
   share-invariant monotonicity proofs (§6, Appendices E–F), plus the `t → 1`
   constant-product limit (Appendix D). Here `y` is simply the total reserve, virtual
   reserves included.
