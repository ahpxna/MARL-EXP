import «LeanStructuralFamilyLowerV1»

/-! # Structural: the UPPER half -- the `m-1` one-defect orderings, built explicitly
for every `m`, so the family law is a theorem and not a census.

`LeanStructuralFamilyLowerV1` proves every ordering of
`g_m = (-3, (-1)^p, (+1)^q, 3)` pays at least 2, and that a uniform mixture of `b`
one-defect orderings attains both lower bounds.  `scripts/P14_structural_family_allm.py`
checks the orderings exist for `m = 5..150`.  This file CONSTRUCTS them for every
`p, q` with `q ≤ p ≤ q+1`, which is every `m ≥ 5`.

## THE CONSTRUCTION

`altFrom` is the greedy alternation: from the current prefix sum, move back towards 0
using a `-1` when the sum is `≥ 0` and a `+1` when it is `< 0`.  `altFrom_defects`
proves the invariant `|s| ≤ 1 ∧ |s - a + b| ≤ 1` is preserved, so an alternating block
pays NOTHING.  Both orderings are then `block ++ [±3, ∓3] ++ block`:

    j = 2t+1 :  altFrom 0 t t      ++ [-3, 3] ++ altFrom 0 (p-t) (q-t)
    j = 2t   :  altFrom 0 t (t-1)  ++ [ 3,-3] ++ altFrom (-1) (p-t) (q+1-t)

In the odd case the first block ends at 0 and `-3` takes the sum to `-3`: defect
`3 - 1 = 2` at budget `2t+1`, and `+3` returns it to 0.  In the even case the first
block has ODD length and ends at `-1` (a block ending at 0 must have even length, by
parity -- which is why the two cases are genuinely different), and `+3` takes the sum
to `2`: defect `2 - 0 = 2` at budget `2t`.  Every other budget is in `{-1,0,1}`.

## WHAT IS PROVED

* `altFrom_multiset` — the alternating block uses exactly `a` copies of `-1` and `b`
  copies of `+1`; this is pure counting and needs no invariant.
* `altFrom_sum`, `altFrom_length`.
* `altFrom_defects` — under the invariant, EVERY budget inside the block is free.
* `orderOdd_multiset`, `orderEven_multiset` — both orderings are permutations of `g_m`.
* `orderOdd_defects`, `orderEven_defects` — the defect profile is `0…0, 2, 0…0`.
* `exists_one_defect` — **for every `m ≥ 5` and every budget `j ∈ {1,…,m-1}` there is
  a permutation of `g_m` whose only defect is at `j`, and it equals 2.**
* `totalDefect_orderOdd`, `totalDefect_orderEven` — each pays exactly 2, matching the
  lower bound of `two_le_totalDefect`, so no ordering does better.

## WHAT THIS DOES NOT ESTABLISH

- The normalisation `D = ∑|g_i| = m+4` and the reading of `dfc s_k` as the regret
  `(|s_k| - k mod 2)/D` are `parity_bridge` plus arithmetic, not re-derived here.
- The mixture step (uniform over the `m-1` orderings) is `avg_achieved`/`path_achieved`
  in the lower module.
- `V_path/V_avg = m-1` grows, but the level `2/(m+4)` falls: this is NOT a separation
  at a fixed normalised `ε`.
-/

namespace CIGAMF.P13.StructuralFamilyUpper

open CIGAMF.P13.StructuralFamilyLower

/-- Greedy alternation: always step back towards 0. -/
def altFrom : ℕ → ℤ → ℕ → ℕ → List ℤ
  | 0, _, _, _ => []
  | n + 1, s, a, b =>
      if 0 ≤ s then
        (if a = 0 then (1 : ℤ) :: altFrom n (s + 1) a (b - 1)
         else (-1 : ℤ) :: altFrom n (s - 1) (a - 1) b)
      else
        (if b = 0 then (-1 : ℤ) :: altFrom n (s - 1) (a - 1) b
         else (1 : ℤ) :: altFrom n (s + 1) a (b - 1))

theorem altFrom_multiset : ∀ (n : ℕ) (s : ℤ) (a b : ℕ), n = a + b →
    ((altFrom n s a b : List ℤ) : Multiset ℤ)
      = Multiset.replicate a (-1) + Multiset.replicate b 1 := by
  intro n
  induction n with
  | zero =>
      intro s a b hn
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; simp [altFrom]
  | succ n ih =>
      intro s a b hn
      have hcons : ∀ (x : ℤ) (l : List ℤ),
          ((x :: l : List ℤ) : Multiset ℤ) = x ::ₘ (l : Multiset ℤ) := fun _ _ => rfl
      by_cases hsge : (0:ℤ) ≤ s
      · by_cases ha0 : a = 0
        · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          subst ha0
          rw [show altFrom (n+1) s 0 (b'+1)
                = (1 : ℤ) :: altFrom n (s+1) 0 (b'+1-1) by simp [altFrom, hsge]]
          simp only [Nat.add_sub_cancel]
          rw [hcons, ih (s+1) 0 b' (by omega)]
          simp [Multiset.replicate_succ]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          rw [show altFrom (n+1) s (a'+1) b
                = (-1 : ℤ) :: altFrom n (s-1) (a'+1-1) b by simp [altFrom, hsge, ha0]]
          simp only [Nat.add_sub_cancel]
          rw [hcons, ih (s-1) a' b (by omega)]
          simp [Multiset.replicate_succ]
      · by_cases hb0 : b = 0
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          subst hb0
          rw [show altFrom (n+1) s (a'+1) 0
                = (-1 : ℤ) :: altFrom n (s-1) (a'+1-1) 0 by simp [altFrom, hsge]]
          simp only [Nat.add_sub_cancel]
          rw [hcons, ih (s-1) a' 0 (by omega)]
          simp [Multiset.replicate_succ]
        · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          rw [show altFrom (n+1) s a (b'+1)
                = (1 : ℤ) :: altFrom n (s+1) a (b'+1-1) by simp [altFrom, hsge, hb0]]
          simp only [Nat.add_sub_cancel]
          rw [hcons, ih (s+1) a b' (by omega)]
          simp [Multiset.replicate_succ]

theorem altFrom_sum (n : ℕ) (s : ℤ) (a b : ℕ) (hn : n = a + b) :
    (altFrom n s a b).sum = -(a:ℤ) + (b:ℤ) := by
  have h := altFrom_multiset n s a b hn
  have : ((altFrom n s a b : List ℤ) : Multiset ℤ).sum
      = (Multiset.replicate a (-1) + Multiset.replicate b (1:ℤ)).sum := by rw [h]
  simpa [Multiset.sum_replicate, nsmul_eq_mul] using this

theorem altFrom_length (n : ℕ) (s : ℤ) (a b : ℕ) (hn : n = a + b) :
    (altFrom n s a b).length = n := by
  have h := altFrom_multiset n s a b hn
  have : ((altFrom n s a b : List ℤ) : Multiset ℤ).card
      = (Multiset.replicate a (-1) + Multiset.replicate b (1:ℤ)).card := by rw [h]
  simpa [hn] using this

/-- The invariant: an alternating block never leaves `{-1,0,1}`, so it is free. -/
theorem altFrom_defects : ∀ (n : ℕ) (s : ℤ) (a b : ℕ), n = a + b → |s| ≤ 1 →
    |s - (a:ℤ) + (b:ℤ)| ≤ 1 →
    defects s (altFrom n s a b) = List.replicate n 0 := by
  intro n
  induction n with
  | zero =>
      intro s a b hn _ _
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; simp [altFrom, defects]
  | succ n ih =>
      intro s a b hn hs he
      by_cases hsge : (0:ℤ) ≤ s
      · by_cases ha0 : a = 0
        · -- forced: s = 0, b = 1, n = 0
          subst ha0
          have hb1 : b = n + 1 := by omega
          have hbpos : 1 ≤ (b:ℤ) := by omega
          have habs := abs_le.1 he
          have hs0 : s = 0 := by push_cast at habs ⊢; omega
          have hbeq : b = 1 := by
            have : (b:ℤ) ≤ 1 := by push_cast at habs; omega
            omega
          have hn0 : n = 0 := by omega
          subst hs0; subst hn0
          rw [show altFrom (0+1) (0:ℤ) 0 b = (1 : ℤ) :: altFrom 0 1 0 (b-1) by
                simp [altFrom]]
          simp [defects, dfc_one, altFrom]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hsub : |s - 1| ≤ 1 := by
            have := abs_le.1 hs; rw [abs_le]; omega
          have hnext : |(s - 1) - (a':ℤ) + (b:ℤ)| ≤ 1 := by
            have := abs_le.1 he; rw [abs_le]; push_cast at this ⊢; omega
          rw [show altFrom (n+1) s (a'+1) b
                = (-1 : ℤ) :: altFrom n (s-1) (a'+1-1) b by simp [altFrom, hsge, ha0]]
          simp only [Nat.add_sub_cancel]
          have hstep : s + (-1 : ℤ) = s - 1 := by ring
          rw [show defects s ((-1 : ℤ) :: altFrom n (s-1) a' b)
                = dfc (s + (-1)) :: defects (s + (-1)) (altFrom n (s-1) a' b) from rfl,
             hstep, ih (s-1) a' b (by omega) hsub hnext,
             (dfc_eq_zero_iff (s-1)).2 hsub]
          rfl
      · push_neg at hsge
        by_cases hb0 : b = 0
        · exfalso
          subst hb0
          have hapos : 1 ≤ (a:ℤ) := by omega
          have := abs_le.1 he
          have := abs_le.1 hs
          push_cast at *
          omega
        · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          have hsub : |s + 1| ≤ 1 := by
            have := abs_le.1 hs; rw [abs_le]; omega
          have hnext : |(s + 1) - (a:ℤ) + (b':ℤ)| ≤ 1 := by
            have := abs_le.1 he; rw [abs_le]; push_cast at this ⊢; omega
          rw [show altFrom (n+1) s a (b'+1)
                = (1 : ℤ) :: altFrom n (s+1) a (b'+1-1) by
                  simp [altFrom, not_le.2 hsge, hb0]]
          simp only [Nat.add_sub_cancel]
          rw [show defects s ((1 : ℤ) :: altFrom n (s+1) a b')
                = dfc (s + 1) :: defects (s + 1) (altFrom n (s+1) a b') from rfl,
             ih (s+1) a b' (by omega) hsub hnext,
             (dfc_eq_zero_iff (s+1)).2 hsub]
          rfl

/-- The family, as a multiset. -/
def gList (p q : ℕ) : List ℤ :=
  (-3) :: 3 :: (List.replicate p (-1) ++ List.replicate q 1)

/-- The ordering whose single defect sits at the odd budget `j = 2t+1`. -/
def orderOdd (t p q : ℕ) : List ℤ :=
  altFrom (t + t) 0 t t ++ (-3) :: 3 :: altFrom ((p - t) + (q - t)) 0 (p - t) (q - t)

/-- The ordering whose single defect sits at the even budget `j = 2t`. -/
def orderEven (t p q : ℕ) : List ℤ :=
  altFrom (t + (t - 1)) 0 t (t - 1)
    ++ 3 :: (-3) :: altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t)

theorem orderOdd_multiset (t p q : ℕ) (htp : t ≤ p) (htq : t ≤ q) :
    ((orderOdd t p q : List ℤ) : Multiset ℤ) = ((gList p q : List ℤ) : Multiset ℤ) := by
  have h1 := altFrom_multiset (t + t) 0 t t rfl
  have h2 := altFrom_multiset ((p - t) + (q - t)) 0 (p - t) (q - t) rfl
  have hp : t + (p - t) = p := by omega
  have hq : t + (q - t) = q := by omega
  unfold orderOdd gList
  rw [← Multiset.coe_add, h1]
  have hcons : ∀ (x : ℤ) (l : List ℤ),
      ((x :: l : List ℤ) : Multiset ℤ) = x ::ₘ (l : Multiset ℤ) := fun _ _ => rfl
  rw [hcons, hcons, h2, hcons, hcons, ← Multiset.coe_add,
      Multiset.coe_replicate, Multiset.coe_replicate]
  have hpr : Multiset.replicate p (-1 : ℤ)
      = Multiset.replicate t (-1) + Multiset.replicate (p - t) (-1) := by
    rw [← Multiset.replicate_add, hp]
  have hqr : Multiset.replicate q (1 : ℤ)
      = Multiset.replicate t 1 + Multiset.replicate (q - t) 1 := by
    rw [← Multiset.replicate_add, hq]
  rw [hpr, hqr]
  simp only [← Multiset.singleton_add]
  abel

theorem orderEven_multiset (t p q : ℕ) (ht : 1 ≤ t) (htp : t ≤ p) (htq : t ≤ q + 1) :
    ((orderEven t p q : List ℤ) : Multiset ℤ) = ((gList p q : List ℤ) : Multiset ℤ) := by
  have h1 := altFrom_multiset (t + (t - 1)) 0 t (t - 1) rfl
  have h2 := altFrom_multiset ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t) rfl
  have hp : t + (p - t) = p := by omega
  have hq : (t - 1) + (q + 1 - t) = q := by omega
  unfold orderEven gList
  rw [← Multiset.coe_add, h1]
  have hcons : ∀ (x : ℤ) (l : List ℤ),
      ((x :: l : List ℤ) : Multiset ℤ) = x ::ₘ (l : Multiset ℤ) := fun _ _ => rfl
  rw [hcons, hcons, h2, hcons, hcons, ← Multiset.coe_add,
      Multiset.coe_replicate, Multiset.coe_replicate]
  have hpr : Multiset.replicate p (-1 : ℤ)
      = Multiset.replicate t (-1) + Multiset.replicate (p - t) (-1) := by
    rw [← Multiset.replicate_add, hp]
  have hqr : Multiset.replicate q (1 : ℤ)
      = Multiset.replicate (t - 1) 1 + Multiset.replicate (q + 1 - t) 1 := by
    rw [← Multiset.replicate_add, hq]
  rw [hpr, hqr]
  simp only [← Multiset.singleton_add]
  abel

theorem orderOdd_defects (t p q : ℕ) (htp : t ≤ p) (htq : t ≤ q)
    (hpq : q ≤ p) (hqp : p ≤ q + 1) :
    defects 0 (orderOdd t p q)
      = List.replicate (t + t) 0 ++ (2 : ℤ) :: List.replicate ((p - t) + (q - t) + 1) 0 := by
  have hA : defects (0:ℤ) (altFrom (t + t) 0 t t) = List.replicate (t + t) 0 :=
    altFrom_defects (t + t) 0 t t rfl (by norm_num) (by push_cast; simp)
  have hAs : (altFrom (t + t) 0 t t).sum = 0 := by
    rw [altFrom_sum (t + t) 0 t t rfl]; ring
  have hBinv : |(0:ℤ) - ((p - t : ℕ):ℤ) + ((q - t : ℕ):ℤ)| ≤ 1 := by
    have hc1 : ((p - t : ℕ):ℤ) = (p:ℤ) - (t:ℤ) := by omega
    have hc2 : ((q - t : ℕ):ℤ) = (q:ℤ) - (t:ℤ) := by omega
    rw [hc1, hc2, abs_le]; constructor <;> [skip; skip] <;> omega
  have hB : defects (0:ℤ) (altFrom ((p - t) + (q - t)) 0 (p - t) (q - t))
      = List.replicate ((p - t) + (q - t)) 0 :=
    altFrom_defects _ 0 (p - t) (q - t) rfl (by norm_num) hBinv
  unfold orderOdd
  rw [defects_append, hA, hAs]
  have hmid : defects ((0:ℤ) + 0)
        ((-3 : ℤ) :: 3 :: altFrom ((p - t) + (q - t)) 0 (p - t) (q - t))
      = (2 : ℤ) :: (0 : ℤ) :: List.replicate ((p - t) + (q - t)) 0 := by
    have e0 : (0:ℤ) + 0 + (-3) = -3 := by ring
    have e1 : (-3:ℤ) + 3 = 0 := by ring
    rw [show defects ((0:ℤ) + 0)
            ((-3 : ℤ) :: 3 :: altFrom ((p - t) + (q - t)) 0 (p - t) (q - t))
          = dfc ((0:ℤ) + 0 + (-3)) :: defects ((0:ℤ) + 0 + (-3))
              ((3:ℤ) :: altFrom ((p - t) + (q - t)) 0 (p - t) (q - t)) from rfl, e0]
    rw [show defects (-3 : ℤ) ((3:ℤ) :: altFrom ((p - t) + (q - t)) 0 (p - t) (q - t))
          = dfc ((-3:ℤ) + 3) :: defects ((-3:ℤ) + 3)
              (altFrom ((p - t) + (q - t)) 0 (p - t) (q - t)) from rfl, e1]
    rw [dfc_neg_three, dfc_zero, hB]
  rw [hmid]
  simp [List.replicate_succ]

theorem orderEven_defects (t p q : ℕ) (ht : 1 ≤ t) (htp : t ≤ p) (htq : t ≤ q + 1)
    (hpq : q ≤ p) (hqp : p ≤ q + 1) :
    defects 0 (orderEven t p q)
      = List.replicate (t + (t - 1)) 0
        ++ (2 : ℤ) :: List.replicate ((p - t) + (q + 1 - t) + 1) 0 := by
  have hAinv : |(0:ℤ) - (t:ℤ) + ((t - 1 : ℕ):ℤ)| ≤ 1 := by
    have hc : ((t - 1 : ℕ):ℤ) = (t:ℤ) - 1 := by omega
    rw [hc, abs_le]; constructor <;> omega
  have hA : defects (0:ℤ) (altFrom (t + (t - 1)) 0 t (t - 1))
      = List.replicate (t + (t - 1)) 0 :=
    altFrom_defects _ 0 t (t - 1) rfl (by norm_num) hAinv
  have hAs : (altFrom (t + (t - 1)) 0 t (t - 1)).sum = -1 := by
    rw [altFrom_sum (t + (t - 1)) 0 t (t - 1) rfl]
    have hc : ((t - 1 : ℕ):ℤ) = (t:ℤ) - 1 := by omega
    rw [hc]; ring
  have hBinv : |(-1:ℤ) - ((p - t : ℕ):ℤ) + ((q + 1 - t : ℕ):ℤ)| ≤ 1 := by
    have hc1 : ((p - t : ℕ):ℤ) = (p:ℤ) - (t:ℤ) := by omega
    have hc2 : ((q + 1 - t : ℕ):ℤ) = (q:ℤ) + 1 - (t:ℤ) := by omega
    rw [hc1, hc2, abs_le]; constructor <;> omega
  have hB : defects (-1:ℤ) (altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t))
      = List.replicate ((p - t) + (q + 1 - t)) 0 :=
    altFrom_defects _ (-1) (p - t) (q + 1 - t) rfl (by norm_num) hBinv
  unfold orderEven
  rw [defects_append, hA, hAs]
  have hmid : defects ((0:ℤ) + -1) ((3 : ℤ) :: (-3 : ℤ) ::
        altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t))
      = (2 : ℤ) :: (0 : ℤ) :: List.replicate ((p - t) + (q + 1 - t)) 0 := by
    have e0 : (0:ℤ) + -1 + 3 = 2 := by ring
    have e1 : (2:ℤ) + -3 = -1 := by ring
    rw [show defects ((0:ℤ) + -1) ((3 : ℤ) :: (-3 : ℤ) ::
            altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t))
          = dfc ((0:ℤ) + -1 + 3) :: defects ((0:ℤ) + -1 + 3)
              ((-3:ℤ) :: altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t))
          from rfl, e0]
    rw [show defects (2 : ℤ) ((-3:ℤ) :: altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t))
          = dfc ((2:ℤ) + -3) :: defects ((2:ℤ) + -3)
              (altFrom ((p - t) + (q + 1 - t)) (-1) (p - t) (q + 1 - t)) from rfl, e1]
    rw [dfc_two, dfc_neg_one, hB]
  rw [hmid]
  simp [List.replicate_succ]

theorem totalDefect_orderOdd (t p q : ℕ) (htp : t ≤ p) (htq : t ≤ q)
    (hpq : q ≤ p) (hqp : p ≤ q + 1) : totalDefect 0 (orderOdd t p q) = 2 := by
  unfold totalDefect
  rw [orderOdd_defects t p q htp htq hpq hqp]
  simp

theorem totalDefect_orderEven (t p q : ℕ) (ht : 1 ≤ t) (htp : t ≤ p) (htq : t ≤ q + 1)
    (hpq : q ≤ p) (hqp : p ≤ q + 1) : totalDefect 0 (orderEven t p q) = 2 := by
  unfold totalDefect
  rw [orderEven_defects t p q ht htp htq hpq hqp]
  simp

/-- **For every budget there is an ordering that pays only there.**  `m = p+q+2 ≥ 5`,
`j` ranges over `1 … m-1`, and the defect profile is `0…0, 2, 0…0` with the `2` at
position `j`. -/
theorem exists_one_defect (p q j : ℕ) (hpq : q ≤ p) (hqp : p ≤ q + 1)
    (hj1 : 1 ≤ j) (hjm : j ≤ p + q + 1) :
    ∃ l : List ℤ, ((l : List ℤ) : Multiset ℤ) = ((gList p q : List ℤ) : Multiset ℤ)
      ∧ defects 0 l = List.replicate (j - 1) 0
          ++ (2 : ℤ) :: List.replicate (p + q + 2 - j) 0 := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht1 : 1 ≤ t := by omega
    have htp : t ≤ p := by omega
    have htq : t ≤ q + 1 := by omega
    refine ⟨orderEven t p q, orderEven_multiset t p q ht1 htp htq, ?_⟩
    rw [orderEven_defects t p q ht1 htp htq hpq hqp]
    have e1 : t + (t - 1) = j - 1 := by omega
    have e2 : (p - t) + (q + 1 - t) + 1 = p + q + 2 - j := by omega
    rw [e1, e2]
  · obtain ⟨t, ht⟩ := ho
    have htq : t ≤ q := by omega
    have htp : t ≤ p := by omega
    refine ⟨orderOdd t p q, orderOdd_multiset t p q htp htq, ?_⟩
    rw [orderOdd_defects t p q htp htq hpq hqp]
    have e1 : t + t = j - 1 := by omega
    have e2 : (p - t) + (q - t) + 1 = p + q + 2 - j := by omega
    rw [e1, e2]

#print axioms altFrom_multiset
#print axioms altFrom_sum
#print axioms altFrom_length
#print axioms altFrom_defects
#print axioms orderOdd_multiset
#print axioms orderEven_multiset
#print axioms orderOdd_defects
#print axioms orderEven_defects
#print axioms totalDefect_orderOdd
#print axioms totalDefect_orderEven
#print axioms exists_one_defect

end CIGAMF.P13.StructuralFamilyUpper
