import Mathlib

/-! # Functional: the three finite witnesses of the extrema/gap crossover.

THE FAMILY. Incumbent `I` has two cells with means `-1/2, 1/2`, so capacity `1`.
Outsider `O` has `n+2` cells: two endpoints at `±rho/2` and `n` middle cells at
`0`, so capacity `rho`. Gaussian variance `1`, one unit of cost per cell, every
mean free to move, allocation `w` with total mass `1`. An alternative flips the
Top-1 when `capacity(O) ≥ capacity(I)`.

WHAT IS PROVED HERE. Three explicit flipping alternatives and their exact
energies, and the finite upper bound they give on the game information:

    witness EE  move all four endpoints to `±(1+rho)/4`   energy `(1-u)(1-rho)^2/32`
    witness MM  move two middle cells to `±1/2`           energy `(w a + w b)/8`
    witness EM  move one middle cell to `1-rho/2`         energy `w a (1-rho/2)^2/2`

    `crossover_upper` :  for EVERY allocation there is a flipping alternative of
    energy at most  `kappa (1-rho)^2 / (32 kappa + n (1-rho)^2)`,
    `kappa rho = min (1/4) ((1-rho/2)^2/2)`.

Since the game information is an infimum over flipping alternatives, exhibiting
one alternative bounds it from above; no infimum is defined here, and NOTHING
here bounds it from below. The two limit laws
`n Gamma_n -> kappa` (fixed `rho`) and `n Gamma_n -> c^2/(8(c^2+4))`
(at `rho = 1 - c/sqrt n`) are NOT proved here: they need matching lower bounds,
and at present they are numerical evidence only
(`scripts/N7_functional_extrema_crossover.py`).

The bound is a RELAXATION twice over: the order-statistic step replaces the two
lightest middle cells by the average, and the witnesses are three particular
alternatives, not the whole alternative set. Measured tightness against the true
optimum runs 0.75-0.999 over the grid in that script.
-/

namespace CIGAMF.P13.FunctionalExtremaCrossover
open scoped BigOperators
open Finset
noncomputable section

variable {n : ℕ}

/-- The two outsider endpoints. -/
def e0 (n : ℕ) : Fin (n+2) := ⟨0, by omega⟩
def e1 (n : ℕ) : Fin (n+2) := ⟨1, by omega⟩

/-- A cell is a middle cell when its index is at least `2`. -/
def IsMiddle (a : Fin (n+2)) : Prop := 2 ≤ a.val

/-- Outsider means: `±rho/2` at the two endpoints, `0` on every middle cell. -/
def meanO (rho : ℝ) (n : ℕ) (a : Fin (n+2)) : ℝ :=
  if a.val = 0 then rho/2 else if a.val = 1 then -rho/2 else 0

theorem meanO_e0 (rho : ℝ) : meanO rho n (e0 n) = rho/2 := by simp [meanO, e0]
theorem meanO_e1 (rho : ℝ) : meanO rho n (e1 n) = -rho/2 := by simp [meanO, e1]
theorem meanO_middle (rho : ℝ) {a : Fin (n+2)} (ha : IsMiddle a) : meanO rho n a = 0 := by
  unfold meanO IsMiddle at *
  rw [if_neg (by omega), if_neg (by omega)]

theorem e0_ne_e1 : e0 n ≠ e1 n := by
  simp [e0, e1, Fin.ext_iff]

theorem middle_ne_e0 {a : Fin (n+2)} (ha : IsMiddle a) : a ≠ e0 n := by
  intro h; rw [h] at ha; exact absurd ha (by simp [e0, IsMiddle])

theorem middle_ne_e1 {a : Fin (n+2)} (ha : IsMiddle a) : a ≠ e1 n := by
  intro h; rw [h] at ha; exact absurd ha (by simp [e1, IsMiddle])

/-- The outsider's capacity. -/
def rangeO (lO : Fin (n+2) → ℝ) : ℝ :=
  univ.sup' univ_nonempty lO - univ.inf' univ_nonempty lO

theorem sub_le_rangeO (lO : Fin (n+2) → ℝ) (a b : Fin (n+2)) :
    lO a - lO b ≤ rangeO lO :=
  sub_le_sub (le_sup' lO (mem_univ a)) (inf'_le lO (mem_univ b))

/-- The alternative reverses the Top-1: `capacity O ≥ capacity I`, where the
two-cell incumbent's capacity is `|lI1 - lI0|`. -/
def Flips (lI0 lI1 : ℝ) (lO : Fin (n+2) → ℝ) : Prop := |lI1 - lI0| ≤ rangeO lO

/-- Energy of an alternative: half the weighted squared displacement. -/
def energy (wI0 wI1 : ℝ) (wO : Fin (n+2) → ℝ) (rho : ℝ)
    (lI0 lI1 : ℝ) (lO : Fin (n+2) → ℝ) : ℝ :=
  (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)/2 + (∑ a, wO a*(lO a - meanO rho n a)^2)/2

/-- Sum of a family supported on `{a, b}`. -/
theorem sum_supported_pair {a b : Fin (n+2)} (hab : a ≠ b) (f : Fin (n+2) → ℝ)
    (h : ∀ c, c ≠ a → c ≠ b → f c = 0) : ∑ c, f c = f a + f b := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ {a, b})
      (fun c _ hc => h c (by simpa using fun h' => hc (by simp [h']))
        (by intro h'; exact hc (by simp [h'])))]
  exact Finset.sum_pair hab

/-! ## Witness EE: move all four endpoints to the common levels `±(1+rho)/4` -/

theorem witness_EE (rho : ℝ) (h0 : 0 ≤ rho) (wI0 wI1 : ℝ) (wO : Fin (n+2) → ℝ) :
    ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
      energy wI0 wI1 wO rho lI0 lI1 lO
        = (wI0 + wI1 + wO (e0 n) + wO (e1 n))*(1-rho)^2/32 := by
  classical
  set f : Fin (n+2) → ℝ :=
    fun a => if a = e0 n then (1+rho)/4 else if a = e1 n then -(1+rho)/4 else 0 with hf
  have hf0 : f (e0 n) = (1+rho)/4 := by simp [hf]
  have hf1 : f (e1 n) = -(1+rho)/4 := by simp [hf, Ne.symm e0_ne_e1]
  have hfz : ∀ c, c ≠ e0 n → c ≠ e1 n → f c = 0 := by
    intro c h0' h1'; simp [hf, h0', h1']
  have hmz : ∀ c : Fin (n+2), c ≠ e0 n → c ≠ e1 n → meanO rho n c = 0 := by
    intro c h0' h1'
    have hv0 : c.val ≠ 0 := fun h => h0' (Fin.ext (by simpa [e0] using h))
    have hv1 : c.val ≠ 1 := fun h => h1' (Fin.ext (by simpa [e1] using h))
    simp [meanO, hv0, hv1]
  refine ⟨-(1+rho)/4, (1+rho)/4, f, ?_, ?_⟩
  · have h := sub_le_rangeO f (e0 n) (e1 n)
    rw [hf0, hf1] at h
    unfold Flips
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (1+rho)/4 - -(1+rho)/4)]
    linarith
  · unfold energy
    have hsum : (∑ a, wO a*(f a - meanO rho n a)^2)
        = wO (e0 n)*((1-rho)/4)^2 + wO (e1 n)*((1-rho)/4)^2 := by
      rw [sum_supported_pair e0_ne_e1 _ (fun c hc0 hc1 => by
        rw [hfz c hc0 hc1, hmz c hc0 hc1]; ring)]
      rw [hf0, hf1, meanO_e0, meanO_e1]
      ring
    rw [hsum]
    ring

/-! ## Witness MM: open two middle cells to `±1/2`, incumbent untouched -/

theorem witness_MM (rho : ℝ) (wI0 wI1 : ℝ) (wO : Fin (n+2) → ℝ)
    {a b : Fin (n+2)} (ha : IsMiddle a) (hb : IsMiddle b) (hab : a ≠ b) :
    ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
      energy wI0 wI1 wO rho lI0 lI1 lO = (wO a + wO b)/8 := by
  classical
  set f : Fin (n+2) → ℝ :=
    fun c => if c = a then 1/2 else if c = b then -1/2 else meanO rho n c with hf
  have hfa : f a = 1/2 := by simp [hf]
  have hfb : f b = -1/2 := by simp [hf, Ne.symm hab]
  refine ⟨-1/2, 1/2, f, ?_, ?_⟩
  · have h := sub_le_rangeO f a b
    rw [hfa, hfb] at h
    unfold Flips
    rw [show (1:ℝ)/2 - -1/2 = 1 by ring, abs_one]
    linarith
  · unfold energy
    have hsum : (∑ c, wO c*(f c - meanO rho n c)^2)
        = wO a*(1/2 - meanO rho n a)^2 + wO b*(-1/2 - meanO rho n b)^2 := by
      rw [sum_supported_pair hab _ (fun c hc0 hc1 => by simp [hf, hc0, hc1])]
      rw [hfa, hfb]
    rw [hsum, meanO_middle rho ha, meanO_middle rho hb]
    ring

/-! ## Witness EM: push one middle cell to `1 - rho/2`, against the endpoint `-rho/2` -/

theorem witness_EM (rho : ℝ) (wI0 wI1 : ℝ) (wO : Fin (n+2) → ℝ)
    {a : Fin (n+2)} (ha : IsMiddle a) :
    ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
      energy wI0 wI1 wO rho lI0 lI1 lO = wO a*(1-rho/2)^2/2 := by
  classical
  set f : Fin (n+2) → ℝ := fun c => if c = a then 1-rho/2 else meanO rho n c with hf
  have hfa : f a = 1-rho/2 := by simp [hf]
  have hfe1 : f (e1 n) = -rho/2 := by
    rw [hf]
    simp only [if_neg (Ne.symm (middle_ne_e1 ha)), meanO_e1]
  refine ⟨-1/2, 1/2, f, ?_, ?_⟩
  · have h := sub_le_rangeO f a (e1 n)
    rw [hfa, hfe1] at h
    unfold Flips
    rw [show (1:ℝ)/2 - -1/2 = 1 by ring, abs_one]
    linarith
  · unfold energy
    have hsum : (∑ c, wO c*(f c - meanO rho n c)^2) = wO a*(1-rho/2 - meanO rho n a)^2 := by
      rw [Finset.sum_eq_single a (fun c _ hc => by simp [hf, hc]) (by simp)]
      rw [hfa]
    rw [hsum, meanO_middle rho ha]
    ring

/-! ## The middle cells carry `n` of the `n+2` coordinates -/

/-- The middle cells, as the complement of the two endpoints. Defining them by
`sdiff` rather than by `filter` keeps `IsMiddle` free of a decidability
instance. -/
def middles (n : ℕ) : Finset (Fin (n+2)) := univ \ {e0 n, e1 n}

theorem mem_middles {a : Fin (n+2)} : a ∈ middles n ↔ IsMiddle a := by
  simp only [middles, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, IsMiddle, e0, e1, Fin.ext_iff, not_or]
  omega

theorem card_middles : (middles n).card = n := by
  rw [middles, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_insert_of_notMem (by simp [e0_ne_e1]), Finset.card_singleton]
  omega

theorem sum_split (wO : Fin (n+2) → ℝ) :
    ∑ a, wO a = wO (e0 n) + wO (e1 n) + ∑ a ∈ middles n, wO a := by
  rw [middles, ← Finset.sum_sdiff (Finset.subset_univ ({e0 n, e1 n} : Finset (Fin (n+2)))),
    Finset.sum_pair e0_ne_e1]
  ring

/-! ## Order statistics: the lightest middle cell, and the lightest pair -/

theorem exists_light_one (wO : Fin (n+2) → ℝ) (hn : 1 ≤ n) :
    ∃ a, IsMiddle a ∧ (n:ℝ)*wO a ≤ ∑ c ∈ middles n, wO c := by
  classical
  have hne : (middles n).Nonempty := by
    rw [← Finset.card_pos, card_middles]; omega
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (middles n) wO hne
  refine ⟨a, mem_middles.mp ha, ?_⟩
  have h : ∑ _c ∈ middles n, wO a ≤ ∑ c ∈ middles n, wO c :=
    Finset.sum_le_sum (fun c hc => hmin c hc)
  rwa [Finset.sum_const, card_middles, nsmul_eq_mul] at h

theorem exists_light_pair (wO : Fin (n+2) → ℝ) (hn : 2 ≤ n) :
    ∃ a b, IsMiddle a ∧ IsMiddle b ∧ a ≠ b ∧
      (n:ℝ)*(wO a + wO b) ≤ 2*∑ c ∈ middles n, wO c := by
  classical
  have hne : (middles n).Nonempty := by
    rw [← Finset.card_pos, card_middles]; omega
  obtain ⟨a, ha, hmina⟩ := Finset.exists_min_image (middles n) wO hne
  have hne2 : ((middles n).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, card_middles]; omega
  obtain ⟨b, hb, hminb⟩ := Finset.exists_min_image ((middles n).erase a) wO hne2
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbm : b ∈ middles n := (Finset.mem_erase.mp hb).2
  have hab' : wO a ≤ wO b := hmina b hbm
  -- split the middle sum into a, b and the rest, and bound the rest by (n-2) * wO b
  have hsplit : ∑ c ∈ middles n, wO c
      = wO a + (wO b + ∑ c ∈ ((middles n).erase a).erase b, wO c) := by
    rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb]
  have hrest : ((n:ℝ)-2)*wO b ≤ ∑ c ∈ ((middles n).erase a).erase b, wO c := by
    have hcard : (((middles n).erase a).erase b).card = n-2 := by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, card_middles]
      omega
    have h : ∑ _c ∈ ((middles n).erase a).erase b, wO b
        ≤ ∑ c ∈ ((middles n).erase a).erase b, wO c :=
      Finset.sum_le_sum (fun c hc => hminb c (Finset.mem_of_mem_erase hc))
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
    have hc : ((n-2 : ℕ) : ℝ) = (n:ℝ)-2 := by
      have h2 : (2:ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rwa [hc] at h
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  refine ⟨a, b, mem_middles.mp ha, mem_middles.mp hbm, Ne.symm hba, ?_⟩
  rw [hsplit]
  nlinarith [hab', hrest, hn2]

/-! ## The finite upper bound the three witnesses give -/

def kappa (rho : ℝ) : ℝ := min (1/4) ((1-rho/2)^2/2)

theorem kappa_pos (rho : ℝ) (h1 : rho < 1) (h0 : 0 ≤ rho) : 0 < kappa rho := by
  unfold kappa
  have h : 0 < (1-rho/2)^2 := pow_pos (by linarith) 2
  exact lt_min (by norm_num) (by linarith)

/-- The whole point of the three witnesses: whatever the allocation does, one of
them is cheap. `u` is the mass on the middle cells. -/
theorem crossover_upper (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1) (hn : 2 ≤ n)
    (wI0 wI1 : ℝ) (wO : Fin (n+2) → ℝ) (hw : wI0 + wI1 + ∑ a, wO a = 1) :
    ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
      energy wI0 wI1 wO rho lI0 lI1 lO
        ≤ kappa rho*(1-rho)^2/(32*kappa rho + n*(1-rho)^2) := by
  classical
  set u : ℝ := ∑ c ∈ middles n, wO c with hu
  set K : ℝ := kappa rho with hK
  have hKpos : 0 < K := kappa_pos rho h1 h0
  have hgap : 0 < (1-rho)^2 := pow_pos (by linarith) 2
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  set V : ℝ := K*(1-rho)^2/(32*K + n*(1-rho)^2) with hV
  have hden : 0 < 32*K + (n:ℝ)*(1-rho)^2 := by nlinarith
  -- the defining identity of V, in cleared form
  have hVdef : V*(32*K + (n:ℝ)*(1-rho)^2) = K*(1-rho)^2 := by
    rw [hV]; field_simp
  by_cases hcase : K*u ≤ (n:ℝ)*V
  · -- the middle branch is the cheap one: kappa * u / n <= V
    obtain ⟨a, b, ha, hb, hab, hpair⟩ := exists_light_pair wO hn
    obtain ⟨c, hc, hone⟩ := exists_light_one wO (by omega)
    rw [← hu] at hpair hone
    rcases le_total ((1:ℝ)/4) ((1-rho/2)^2/2) with hmin | hmin
    · -- kappa = 1/4 : two middle cells to ±1/2, cost (wO a + wO b)/8 <= u/(4n)
      obtain ⟨lI0, lI1, lO, hflip, heq⟩ := witness_MM rho wI0 wI1 wO ha hb hab
      refine ⟨lI0, lI1, lO, hflip, ?_⟩
      rw [heq]
      have hKval : K = 1/4 := by rw [hK]; unfold kappa; exact min_eq_left hmin
      rw [hKval] at hcase
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 8)]
      have h8 : (n:ℝ)*(wO a + wO b) ≤ (n:ℝ)*(8*V) := by nlinarith [hpair, hcase]
      have h9 := le_of_mul_le_mul_left h8 hnpos
      linarith
    · -- kappa = (1-rho/2)^2/2 : one middle cell to 1-rho/2, cost <= u*K/n
      obtain ⟨lI0, lI1, lO, hflip, heq⟩ := witness_EM rho wI0 wI1 wO hc
      refine ⟨lI0, lI1, lO, hflip, ?_⟩
      rw [heq]
      have hKval : K = (1-rho/2)^2/2 := by rw [hK]; unfold kappa; exact min_eq_right hmin
      have hsq : 0 ≤ (1-rho/2)^2 := sq_nonneg _
      have hstep : wO c*(1-rho/2)^2/2 ≤ u*K/n := by
        rw [hKval, le_div_iff₀ hnpos]
        nlinarith [hone, hsq]
      have hfin : u*K/(n:ℝ) ≤ V := by
        rw [div_le_iff₀ hnpos]; nlinarith [hcase]
      linarith
  · -- the middle branch is expensive, so the endpoint branch is cheap: use EE
    push_neg at hcase
    obtain ⟨lI0, lI1, lO, hflip, heq⟩ := witness_EE rho h0 wI0 wI1 wO
    refine ⟨lI0, lI1, lO, hflip, ?_⟩
    rw [heq]
    have hmass : wI0 + wI1 + wO (e0 n) + wO (e1 n) = 1 - u := by
      rw [sum_split wO] at hw; rw [hu]; linarith
    rw [hmass, div_le_iff₀ (by norm_num : (0:ℝ) < 32)]
    -- n V < K u, and V (32 K + n g) = K g, so K g (1-u) < 32 K V
    have hmul : (n:ℝ)*V*(1-rho)^2 < K*u*(1-rho)^2 :=
      (mul_lt_mul_of_pos_right hcase hgap)
    nlinarith [hVdef, hmul, hKpos, hgap]

#print axioms witness_EE
#print axioms witness_MM
#print axioms witness_EM
#print axioms card_middles
#print axioms exists_light_one
#print axioms exists_light_pair
#print axioms crossover_upper

end
end CIGAMF.P13.FunctionalExtremaCrossover
