import Mathlib

/-!
# Paper C: circular window sums of the odd family, on ℕ

The remaining budgets of the odd construction need the circular window sums.  Working with
`Fin m` arithmetic forces the wrap into the addition; working on `ℕ` with `%` puts it into a
`Finset.range` split instead, which is what this file does.

    W(a, k) = sum over i < k of base((a + i) % m)

splits at `i = m - a`: below it the index is `a + i`, above it `a + i - m`.  So

    W(a, k) = ( P(min(a+k, m)) - P(a) ) + P(a + k - m)     (the last term is 0 when a+k <= m)

with `P` the ordinary prefix sequence.  That identity is the content here.
-/

namespace CIGAMF.P13.PaperCWindow

open Finset

/-- The odd family's weights, indexed on `ℕ` within one period. -/
noncomputable def baseN (j : ℕ) : ℝ :=
  if j = 0 then 3 else if j = 1 then -3 else if j % 2 = 0 then -1 else 1

/-- The ordinary prefix sequence. -/
noncomputable def preN (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, baseN i

theorem preN_zero : preN 0 = 0 := by simp [preN]

theorem preN_succ (j : ℕ) : preN (j + 1) = preN j + baseN j := by
  unfold preN
  rw [Finset.sum_range_succ]

/-- **The prefix pattern**: three values only. -/
theorem preN_pattern : ∀ j, 2 ≤ j → preN j = if j % 2 = 0 then 0 else -1 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro h2
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [preN_succ, preN_succ, preN_zero]
      norm_num [baseN]
    · have hih := ih hn
      rw [preN_succ, hih]
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      rcases Nat.even_or_odd n with he | ho
      · have hpar : n % 2 = 0 := Nat.even_iff.mp he
        rw [if_pos hpar, if_neg (by omega)]
        simp [baseN, h0, h1, hpar]
      · have hpar : n % 2 = 1 := Nat.odd_iff.mp ho
        have hne : n % 2 ≠ 0 := by omega
        rw [if_neg (by omega), if_pos (by omega)]
        simp [baseN, h0, h1, hne]

/-- The circular window sum, on `ℕ`. -/
noncomputable def win (m a k : ℕ) : ℝ := ∑ i ∈ Finset.range k, baseN ((a + i) % m)

/-- **Shifting a prefix**: the sum of `k` terms starting at `a` is the difference of two
prefixes.  This is `Finset.sum_range_add`, named for readability. -/
theorem sum_shift (a k : ℕ) :
    ∑ i ∈ Finset.range k, baseN (a + i) = preN (a + k) - preN a := by
  unfold preN
  rw [Finset.sum_range_add]
  ring

/-- **The window sum, split at the wrap.**  Below the split the index is `a + i`; above it,
`a + i - m`.  The `min` collapses in each branch. -/
theorem win_eq (m a k : ℕ) (hm : 0 < m) (ha : a < m) (hk : k ≤ m) :
    win m a k = (preN (min (a + k) m) - preN a) + preN (a + k - m) := by
  classical
  rcases Nat.lt_or_ge (a + k) (m + 1) with hno | hyes
  · -- no wrap
    have hmin : min (a + k) m = a + k := by omega
    have hsub : a + k - m = 0 := by omega
    rw [hmin, hsub, preN_zero, add_zero]
    have hterm : ∀ i ∈ Finset.range k, baseN ((a + i) % m) = baseN (a + i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.mod_eq_of_lt (by omega)]
    unfold win
    rw [Finset.sum_congr rfl hterm, sum_shift a k]
  · -- wraps: split the range at `m - a`
    have hmin : min (a + k) m = m := by omega
    rw [hmin]
    have hsplit : k = (m - a) + (a + k - m) := by omega
    unfold win
    rw [hsplit, Finset.sum_range_add]
    have hlow : ∀ i ∈ Finset.range (m - a), baseN ((a + i) % m) = baseN (a + i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.mod_eq_of_lt (by omega)]
    have hhigh : ∀ i ∈ Finset.range (a + k - m),
        baseN ((a + ((m - a) + i)) % m) = baseN i := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hidx : a + ((m - a) + i) = m + i := by omega
      rw [hidx, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, sum_shift a (m - a)]
    have hma : a + (m - a) = m := by omega
    rw [hma]
    unfold preN
    have hfix : a + (m - a + (a + k - m)) - m = a + k - m := by omega
    rw [hfix]

/-! ## The prefix at the three kinds of index -/

theorem preN_one : preN 1 = 3 := by
  norm_num [preN, baseN]

theorem preN_even (j : ℕ) (h2 : 2 ≤ j) (hp : j % 2 = 0) : preN j = 0 := by
  rw [preN_pattern j h2, if_pos hp]

theorem preN_odd (j : ℕ) (h2 : 2 ≤ j) (hp : j % 2 = 1) : preN j = -1 := by
  rw [preN_pattern j h2, if_neg (by omega)]

/-- **The alternating prefix sum.**  Over an even number of consecutive indices from `2` on,
the prefix sequence contributes `-1` exactly half the time. -/
theorem preN_alt_sum (t : ℕ) : ∑ i ∈ Finset.range (2 * t), preN (i + 2) = -(t : ℝ) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, preN_even (2 * n + 2) (by omega) (by omega),
      preN_odd (2 * n + 1 + 2) (by omega) (by omega)]
    push_cast
    ring

/-! ## The window at a single rotation -/

/-- No wrap: the window is an ordinary prefix difference. -/
theorem win_noWrap (m a k : ℕ) (hm : 0 < m) (ha : a < m) (h : a + k ≤ m) :
    win m a k = preN (a + k) - preN a := by
  rw [win_eq m a k hm ha (by omega), show min (a + k) m = a + k from by omega,
    show a + k - m = 0 from by omega, preN_zero, add_zero]

/-- Wrap: the window is the whole period less a prefix, plus the wrapped part. -/
theorem win_wrap (m a k : ℕ) (hm : 0 < m) (ha : a < m) (hk : k ≤ m) (h : m < a + k) :
    win m a k = (preN m - preN a) + preN (a + k - m) := by
  rw [win_eq m a k hm ha hk, show min (a + k) m = m from by omega]

/-! ## Summing the absolute windows over all rotations -/

theorem sum_const_one (N : ℕ) (g : ℕ → ℝ) (h : ∀ i ∈ Finset.range N, g i = 1) :
    ∑ i ∈ Finset.range N, g i = (N : ℝ) := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem sum_const_zero (N : ℕ) (g : ℕ → ℝ) (h : ∀ i ∈ Finset.range N, g i = 0) :
    ∑ i ∈ Finset.range N, g i = 0 := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_zero]

/-- **Odd budgets.**  For every odd `k` with `0 < k < m` (and `m` odd, `m ≥ 3`) the total
absolute window mass over the `m` rotations is `m + 4`, independent of `k`. -/
theorem win_abs_sum_odd (m k : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkodd : k % 2 = 1) (hkm : k < m) :
    ∑ a ∈ Finset.range m, |win m a k| = (m : ℝ) + 4 := by
  classical
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · -- `k = 1`: every rotation is a single weight, and there is no wrap.
    have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
    have e0 : win (n + 3) 0 1 = 3 := by
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega), preN_zero, sub_zero]
      exact preN_one
    have e1 : win (n + 3) 1 1 = -3 := by
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega),
        preN_even (1 + 1) (by omega) (by omega), preN_one]
      norm_num
    have eI : ∀ i ∈ Finset.range (n + 1), |win (n + 3) (i + 1 + 1) 1| = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega)]
      rcases Nat.even_or_odd i with he | ho
      · have hp : i % 2 = 0 := Nat.even_iff.mp he
        rw [preN_odd (i + 1 + 1 + 1) (by omega) (by omega),
          preN_even (i + 1 + 1) (by omega) (by omega)]
        norm_num
      · have hp : i % 2 = 1 := Nat.odd_iff.mp ho
        rw [preN_even (i + 1 + 1 + 1) (by omega) (by omega),
          preN_odd (i + 1 + 1) (by omega) (by omega)]
        norm_num
    rw [show n + 3 = (n + 1) + 1 + 1 from by ring, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [Nat.zero_add]
    rw [show (n + 1) + 1 + 1 = n + 3 from by ring, sum_const_one _ _ eI, e0, e1]
    push_cast
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_of_nonpos (by norm_num : (-3:ℝ) ≤ 0)]
    ring
  · -- `k ≥ 3`: two peeled terms in each block, constant `1` in between.
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 3 := ⟨(k - 3) / 2, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, m = 2 * j + 2 * p + 5 := ⟨(m - 2 * j - 5) / 2, by omega⟩
    have hsplit : ∀ f : ℕ → ℝ, ∑ a ∈ Finset.range (2 * j + 2 * p + 5), f a
        = (∑ a ∈ Finset.range (2 * p + 3), f a)
          + ∑ i ∈ Finset.range (2 * j + 2), f (2 * p + 3 + i) := by
      intro f
      have h : (2 * p + 3) + (2 * j + 2) = 2 * j + 2 * p + 5 := by ring
      conv_lhs => rw [← h]
      exact Finset.sum_range_add f _ _
    have hpm : preN (2 * j + 2 * p + 5) = -1 := preN_odd _ (by omega) (by omega)
    have e0 : win (2 * j + 2 * p + 5) 0 (2 * j + 3) = -1 := by
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega), preN_zero, sub_zero]
      exact preN_odd _ (by omega) (by omega)
    have e1 : win (2 * j + 2 * p + 5) 1 (2 * j + 3) = -3 := by
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega),
        preN_even (1 + (2 * j + 3)) (by omega) (by omega), preN_one]
      norm_num
    have eI : ∀ i ∈ Finset.range (2 * p + 1),
        |win (2 * j + 2 * p + 5) (i + 1 + 1) (2 * j + 3)| = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [win_noWrap _ _ _ (by omega) (by omega) (by omega)]
      rcases Nat.even_or_odd i with he | ho
      · have hp : i % 2 = 0 := Nat.even_iff.mp he
        rw [preN_odd (i + 1 + 1 + (2 * j + 3)) (by omega) (by omega),
          preN_even (i + 1 + 1) (by omega) (by omega)]
        norm_num
      · have hp : i % 2 = 1 := Nat.odd_iff.mp ho
        rw [preN_even (i + 1 + 1 + (2 * j + 3)) (by omega) (by omega),
          preN_odd (i + 1 + 1) (by omega) (by omega)]
        norm_num
    have eB0 : win (2 * j + 2 * p + 5) (2 * p + 3) (2 * j + 3) = 3 := by
      rw [win_wrap _ _ _ (by omega) (by omega) (by omega) (by omega), hpm,
        preN_odd (2 * p + 3) (by omega) (by omega),
        show 2 * p + 3 + (2 * j + 3) - (2 * j + 2 * p + 5) = 1 from by omega, preN_one]
      norm_num
    have eBI : ∀ i ∈ Finset.range (2 * j + 1),
        |win (2 * j + 2 * p + 5) (2 * p + 3 + (i + 1)) (2 * j + 3)| = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [win_wrap _ _ _ (by omega) (by omega) (by omega) (by omega), hpm,
        show 2 * p + 3 + (i + 1) + (2 * j + 3) - (2 * j + 2 * p + 5) = i + 2 from by omega]
      rcases Nat.even_or_odd i with he | ho
      · have hp : i % 2 = 0 := Nat.even_iff.mp he
        rw [preN_even (2 * p + 3 + (i + 1)) (by omega) (by omega),
          preN_even (i + 2) (by omega) (by omega)]
        norm_num
      · have hp : i % 2 = 1 := Nat.odd_iff.mp ho
        rw [preN_odd (2 * p + 3 + (i + 1)) (by omega) (by omega),
          preN_odd (i + 2) (by omega) (by omega)]
        norm_num
    have hA : ∑ a ∈ Finset.range (2 * p + 3),
        |win (2 * j + 2 * p + 5) a (2 * j + 3)| = (2 * p + 1 : ℕ) + 3 + 1 := by
      rw [show 2 * p + 3 = (2 * p + 1) + 1 + 1 from by ring, Finset.sum_range_succ',
        Finset.sum_range_succ']
      simp only [Nat.zero_add]
      rw [sum_const_one _ _ eI, e0, e1]
      rw [abs_of_nonpos (by norm_num : (-3:ℝ) ≤ 0), abs_of_nonpos (by norm_num : (-1:ℝ) ≤ 0)]
      ring
    have hB : ∑ i ∈ Finset.range (2 * j + 2),
        |win (2 * j + 2 * p + 5) (2 * p + 3 + i) (2 * j + 3)| = (2 * j + 1 : ℕ) + 3 := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [sum_const_one _ _ eBI, eB0]
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    rw [hsplit (fun a => |win (2 * j + 2 * p + 5) a (2 * j + 3)|), hA, hB]
    push_cast
    ring

/-- **Even budgets.**  For every even `k` with `0 < k < m` the total absolute window mass is
`k + 4` — it grows with the budget instead of being pinned to the period. -/
theorem win_abs_sum_even (m k : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkeven : k % 2 = 0) (hkm : k < m) :
    ∑ a ∈ Finset.range m, |win m a k| = (k : ℝ) + 4 := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 2 := ⟨(k - 2) / 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, m = 2 * j + 2 * q + 3 := ⟨(m - 2 * j - 3) / 2, by omega⟩
  have hsplit : ∀ f : ℕ → ℝ, ∑ a ∈ Finset.range (2 * j + 2 * q + 3), f a
      = (∑ a ∈ Finset.range (2 * q + 2), f a)
        + ∑ i ∈ Finset.range (2 * j + 1), f (2 * q + 2 + i) := by
    intro f
    have h : (2 * q + 2) + (2 * j + 1) = 2 * j + 2 * q + 3 := by ring
    conv_lhs => rw [← h]
    exact Finset.sum_range_add f _ _
  have hpm : preN (2 * j + 2 * q + 3) = -1 := preN_odd _ (by omega) (by omega)
  have e0 : win (2 * j + 2 * q + 3) 0 (2 * j + 2) = 0 := by
    rw [win_noWrap _ _ _ (by omega) (by omega) (by omega), preN_zero, sub_zero]
    exact preN_even _ (by omega) (by omega)
  have e1 : win (2 * j + 2 * q + 3) 1 (2 * j + 2) = -4 := by
    rw [win_noWrap _ _ _ (by omega) (by omega) (by omega),
      preN_odd (1 + (2 * j + 2)) (by omega) (by omega), preN_one]
    norm_num
  have eI : ∀ i ∈ Finset.range (2 * q),
      |win (2 * j + 2 * q + 3) (i + 1 + 1) (2 * j + 2)| = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [win_noWrap _ _ _ (by omega) (by omega) (by omega)]
    rcases Nat.even_or_odd i with he | ho
    · have hp : i % 2 = 0 := Nat.even_iff.mp he
      rw [preN_even (i + 1 + 1 + (2 * j + 2)) (by omega) (by omega),
        preN_even (i + 1 + 1) (by omega) (by omega)]
      norm_num
    · have hp : i % 2 = 1 := Nat.odd_iff.mp ho
      rw [preN_odd (i + 1 + 1 + (2 * j + 2)) (by omega) (by omega),
        preN_odd (i + 1 + 1) (by omega) (by omega)]
      norm_num
  have eB0 : win (2 * j + 2 * q + 3) (2 * q + 2) (2 * j + 2) = 2 := by
    rw [win_wrap _ _ _ (by omega) (by omega) (by omega) (by omega), hpm,
      preN_even (2 * q + 2) (by omega) (by omega),
      show 2 * q + 2 + (2 * j + 2) - (2 * j + 2 * q + 3) = 1 from by omega, preN_one]
    norm_num
  have eBI : ∀ i ∈ Finset.range (2 * j),
      |win (2 * j + 2 * q + 3) (2 * q + 2 + (i + 1)) (2 * j + 2)| = -2 * preN (i + 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [win_wrap _ _ _ (by omega) (by omega) (by omega) (by omega), hpm,
      show 2 * q + 2 + (i + 1) + (2 * j + 2) - (2 * j + 2 * q + 3) = i + 2 from by omega]
    rcases Nat.even_or_odd i with he | ho
    · have hp : i % 2 = 0 := Nat.even_iff.mp he
      rw [preN_odd (2 * q + 2 + (i + 1)) (by omega) (by omega),
        preN_even (i + 2) (by omega) (by omega)]
      norm_num
    · have hp : i % 2 = 1 := Nat.odd_iff.mp ho
      rw [preN_even (2 * q + 2 + (i + 1)) (by omega) (by omega),
        preN_odd (i + 2) (by omega) (by omega)]
      norm_num
  have hA : ∑ a ∈ Finset.range (2 * q + 2),
      |win (2 * j + 2 * q + 3) a (2 * j + 2)| = 4 := by
    rw [show 2 * q + 2 = (2 * q) + 1 + 1 from by ring, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [Nat.zero_add]
    rw [sum_const_zero _ _ eI, e0, e1]
    rw [abs_of_nonpos (by norm_num : (-4:ℝ) ≤ 0)]
    norm_num
  have hB : ∑ i ∈ Finset.range (2 * j + 1),
      |win (2 * j + 2 * q + 3) (2 * q + 2 + i) (2 * j + 2)| = (2 * j : ℝ) + 2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [Finset.sum_congr rfl eBI, ← Finset.mul_sum, preN_alt_sum j, eB0,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  rw [hsplit (fun a => |win (2 * j + 2 * q + 3) a (2 * j + 2)|), hA, hB]
  push_cast
  ring

/-- **The odd budgets dominate.**  Every odd budget carries mass `m + 4`; every even budget
carries `k + 4 ≤ m + 3`.  So the maximum over budgets `0 < k < m` is `m + 4`, attained at
every odd budget and at no even one. -/
theorem win_abs_sum_odd_gt_even (m k k' : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkodd : k % 2 = 1) (hkm : k < m)
    (hk0' : 0 < k') (hkeven' : k' % 2 = 0) (hkm' : k' < m) :
    ∑ a ∈ Finset.range m, |win m a k'| < ∑ a ∈ Finset.range m, |win m a k| := by
  rw [win_abs_sum_odd m k hm3 hmodd hk0 hkodd hkm,
    win_abs_sum_even m k' hm3 hmodd hk0' hkeven' hkm']
  have : (k' : ℝ) < (m : ℝ) := by exact_mod_cast hkm'
  linarith

/-! ## Audit -/

#print axioms preN_alt_sum
#print axioms win_noWrap
#print axioms win_wrap
#print axioms win_abs_sum_odd
#print axioms win_abs_sum_even
#print axioms win_abs_sum_odd_gt_even

/-! ## Audit -/

#print axioms preN_pattern
#print axioms sum_shift
#print axioms win_eq

end CIGAMF.P13.PaperCWindow
