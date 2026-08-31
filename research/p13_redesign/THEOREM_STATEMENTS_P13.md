# P13 theorem statements

## Verified extension target

`variance_plugin_relative_robustness`

For nonnegative coefficients and true standard deviations, positive allocations,
`0 <= rho < 1`, pointwise relative bounds

`(1-rho) sigma_i <= sigmaHat_i <= (1+rho) sigma_i`,

and plug-in optimality of `nHat` against `nStar`, the theorem derives

`V_sigma(nHat) <= ((1+rho)/(1-rho))^2 V_sigma(nStar)`.

The file also provides direct specializations for a directional functional `D`
and for a stable-extrema `C` contrast.

## Open conjectures (not verified)

1. D6 half-factor decision bound:
   `decisionRegret <= (m-1) * deltaSquare / 2`.
2. Two-source response/reference budget split with the `2/3` power law.
3. Selected-radius all-optimal-extension defect controlling all-budget nested-chain regret.

