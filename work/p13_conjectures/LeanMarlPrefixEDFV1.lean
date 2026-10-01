import Mathlib

/-!
# One broadcast order for every capacity: the forced-sender case is earliest-deadline-first

Receivers `i : I` have capacities `K i` and FORCED sets `F i` of senders: the receiver is served
only if every sender of `F i` lies in its decoded prefix (in `LeanMarlDecisionDepthV1`, a sender
is forced for a receiver when it is the only sender that splits some local obstruction).  A
broadcast is an injective position map `pos : J → ℕ`; a receiver of capacity `k` decodes the
senders of position `< k`.

## WHAT IS PROVED

* `card_prefix_le` — an injective broadcast puts at most `k` senders in the prefix of length `k`.
* `serves_necessary` — **the counting condition**: if one order serves every receiver, then for
  every `k` the senders forced by receivers of capacity `≤ k` number at most `k`.
* `edf_serves` — **and it is sufficient**: the earliest-deadline-first order (sort senders by the
  smallest capacity of a receiver that forces them, ties by a fixed index) serves every receiver
  whenever the counting condition holds.
* `serves_iff_counting` — the two together.
* `relay_serves_iff` — with one relayed packet, a receiver of capacity `≥ 1` that decodes the head
  `h` (position `0`) sees `insert h R`; every receiver is served iff `⋃ F i ⊆ insert h R`: the
  nested counting condition over all capacities is replaced by ONE inclusion at the head.
* `counting_gap_witness` — capacities `1, 2`, forced sets `{0}`, `{1, 2}`: each receiver alone fits
  its capacity, the counting condition fails at `k = 2` (three forced senders), and the relayed
  packet `{1, 2}` at head `0` serves both.

## WHAT THIS DOES NOT ESTABLISH

- The counting condition with EDF is Jackson's rule for unit jobs with deadlines (1955); the
  content here is its reading on a prefix broadcast with decision-forced senders, not the
  scheduling fact itself.
- General (non-forced) requirements are hitting sets; deciding whether one order serves them is
  NP-hard (`LeanMarlDecisionDepthV1.hitting_embeds_decode`, Karp 1972 cited).
- Static worlds; the relay statement is one forwarded packet, not the freshness dynamics.
-/

namespace CIGAMF.P13.MarlPrefixEDF

open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The senders a receiver of capacity `k` decodes. -/
def prefixD (pos : J → ℕ) (k : ℕ) : Finset J := univ.filter (fun j => pos j < k)

/-- One order serves every receiver. -/
def Serves (pos : J → ℕ) (K : I → ℕ) (F : I → Finset J) : Prop :=
  ∀ i, F i ⊆ prefixD pos (K i)

/-- The senders forced by some receiver of capacity at most `k`. -/
def forcedBy (K : I → ℕ) (F : I → Finset J) (k : ℕ) : Finset J :=
  univ.filter (fun j => ∃ i, K i ≤ k ∧ j ∈ F i)

theorem card_prefix_le (pos : J → ℕ) (hinj : Function.Injective pos) (k : ℕ) :
    (prefixD pos k).card ≤ k := by
  have hsub : (prefixD pos k).image pos ⊆ range k := by
    intro x hx
    simp only [prefixD, mem_image, mem_filter, mem_univ, true_and] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simpa using hj
  calc (prefixD pos k).card = ((prefixD pos k).image pos).card :=
        (card_image_of_injective _ hinj).symm
    _ ≤ (range k).card := card_le_card hsub
    _ = k := card_range k

/-- **The counting condition is necessary.** -/
theorem serves_necessary (pos : J → ℕ) (hinj : Function.Injective pos) (K : I → ℕ)
    (F : I → Finset J) (h : Serves pos K F) (k : ℕ) : (forcedBy K F k).card ≤ k := by
  have hsub : forcedBy K F k ⊆ prefixD pos k := by
    intro j hj
    simp only [forcedBy, mem_filter, mem_univ, true_and] at hj
    obtain ⟨i, hik, hji⟩ := hj
    have := h i hji
    simp only [prefixD, mem_filter, mem_univ, true_and] at this ⊢
    omega
  exact (card_le_card hsub).trans (card_prefix_le pos hinj k)

/-! ## The earliest-deadline-first order -/

/-- The deadline of a sender: the smallest capacity of a receiver forcing it, `n = |J|` if none. -/
noncomputable def deadline (K : I → ℕ) (F : I → Finset J) (j : J) : ℕ :=
  if h : (univ.filter (fun i => j ∈ F i)).Nonempty then
    min ((univ.filter (fun i => j ∈ F i)).inf' h K) (Fintype.card J)
  else Fintype.card J

/-- A fixed injective tie-break below `n`. -/
noncomputable def tie (j : J) : ℕ := (Fintype.equivFin J j : ℕ)

theorem tie_lt (j : J) : tie j < Fintype.card J := (Fintype.equivFin J j).isLt

theorem tie_inj : Function.Injective (tie (J := J)) := by
  intro a b h
  unfold tie at h
  exact (Fintype.equivFin J).injective (Fin.ext h)

/-- Lexicographic key: deadline first, then the tie-break. -/
noncomputable def key (K : I → ℕ) (F : I → Finset J) (j : J) : ℕ :=
  deadline K F j * Fintype.card J + tie j

/-- The EDF position: how many senders have a smaller key. -/
noncomputable def edfPos (K : I → ℕ) (F : I → Finset J) (j : J) : ℕ :=
  (univ.filter (fun x => key K F x < key K F j)).card

theorem key_inj (K : I → ℕ) (F : I → Finset J) : Function.Injective (key K F) := by
  intro a b h
  unfold key at h
  have ha := tie_lt a
  have hb := tie_lt b
  have hn : 0 < Fintype.card J := by omega
  have hdiv : deadline K F a = deadline K F b := by
    have h1 : (deadline K F a * Fintype.card J + tie a) / Fintype.card J = deadline K F a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ha, zero_add]
    have h2 : (deadline K F b * Fintype.card J + tie b) / Fintype.card J = deadline K F b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
    rw [← h1, ← h2, h]
  rw [hdiv] at h
  exact tie_inj (by omega)

theorem edfPos_strictMono (K : I → ℕ) (F : I → Finset J) {a b : J}
    (hab : key K F a < key K F b) : edfPos K F a < edfPos K F b := by
  unfold edfPos
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    omega
  · have : a ∈ univ.filter (fun x => key K F x < key K F a) := hsub (by simpa using hab)
    simp at this

theorem edfPos_inj (K : I → ℕ) (F : I → Finset J) : Function.Injective (edfPos K F) := by
  intro a b h
  by_contra hne
  have hk : key K F a ≠ key K F b := fun hk => hne (key_inj K F hk)
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · exact absurd h (ne_of_lt (edfPos_strictMono K F hlt))
  · exact absurd h (ne_of_gt (edfPos_strictMono K F hlt))

theorem edfPos_lt_card (K : I → ℕ) (F : I → Finset J) (j : J) :
    edfPos K F j < Fintype.card J := by
  unfold edfPos
  have hsub : univ.filter (fun x => key K F x < key K F j) ⊂ univ := by
    refine ⟨subset_univ _, fun h => ?_⟩
    have := h (mem_univ j)
    simp at this
  have := Finset.card_lt_card hsub
  simpa using this

theorem deadline_le (K : I → ℕ) (F : I → Finset J) (i : I) (j : J) (hj : j ∈ F i) :
    deadline K F j ≤ K i := by
  unfold deadline
  have hne : (univ.filter (fun i => j ∈ F i)).Nonempty := ⟨i, by simpa using hj⟩
  rw [dif_pos hne]
  exact (min_le_left _ _).trans (Finset.inf'_le _ (by simpa using hj))

/-- A sender whose deadline is below `n` is forced by a receiver of exactly that capacity. -/
theorem forced_of_deadline_lt (K : I → ℕ) (F : I → Finset J) (x : J)
    (hx : deadline K F x < Fintype.card J) :
    ∃ i, K i = deadline K F x ∧ x ∈ F i := by
  unfold deadline at hx ⊢
  by_cases hne : (univ.filter (fun i => x ∈ F i)).Nonempty
  · rw [dif_pos hne] at hx ⊢
    obtain ⟨i, hi, hie⟩ := Finset.exists_mem_eq_inf' hne K
    refine ⟨i, ?_, by simpa using hi⟩
    rw [hie] at hx ⊢
    omega
  · rw [dif_neg hne] at hx
    omega

/-- **EDF serves every receiver under the counting condition.** -/
theorem edf_serves (K : I → ℕ) (F : I → Finset J)
    (hcount : ∀ k, (forcedBy K F k).card ≤ k) : Serves (edfPos K F) K F := by
  intro i j hj
  simp only [prefixD, mem_filter, mem_univ, true_and]
  have hdl := deadline_le K F i j hj
  by_cases hlarge : Fintype.card J ≤ deadline K F j
  · have := edfPos_lt_card K F j
    omega
  · push_neg at hlarge
    -- every sender with a smaller key has deadline at most that of `j`, hence is forced by a
    -- receiver of capacity at most `deadline j`
    have hsub : univ.filter (fun x => key K F x < key K F j)
        ⊆ (forcedBy K F (deadline K F j)).erase j := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hxj : x ≠ j := by rintro rfl; exact lt_irrefl _ hx
      have hdx : deadline K F x ≤ deadline K F j := by
        by_contra hc
        push_neg at hc
        unfold key at hx
        have := tie_lt x
        have hmul : (deadline K F j + 1) * Fintype.card J ≤ deadline K F x * Fintype.card J :=
          Nat.mul_le_mul_right _ hc
        have := tie_lt j
        nlinarith
      obtain ⟨i', hi', hxi'⟩ := forced_of_deadline_lt K F x (lt_of_le_of_lt hdx hlarge)
      refine mem_erase.mpr ⟨hxj, ?_⟩
      simp only [forcedBy, mem_filter, mem_univ, true_and]
      exact ⟨i', by omega, hxi'⟩
    have hjmem : j ∈ forcedBy K F (deadline K F j) := by
      obtain ⟨i', hi', hji'⟩ := forced_of_deadline_lt K F j hlarge
      simp only [forcedBy, mem_filter, mem_univ, true_and]
      exact ⟨i', by omega, hji'⟩
    have hcard := card_le_card hsub
    rw [card_erase_of_mem hjmem] at hcard
    have := hcount (deadline K F j)
    have hpos : 1 ≤ (forcedBy K F (deadline K F j)).card := card_pos.mpr ⟨j, hjmem⟩
    unfold edfPos
    omega

/-- **One order serves every receiver iff the counting condition holds.** -/
theorem serves_iff_counting (K : I → ℕ) (F : I → Finset J) :
    (∃ pos : J → ℕ, Function.Injective pos ∧ Serves pos K F)
      ↔ ∀ k, (forcedBy K F k).card ≤ k := by
  constructor
  · rintro ⟨pos, hinj, h⟩ k
    exact serves_necessary pos hinj K F h k
  · intro h
    exact ⟨edfPos K F, edfPos_inj K F, edf_serves K F h⟩

/-! ## One relayed packet replaces the nested condition by one inclusion -/

/-- **Relay.**  If every receiver decodes the head `h` and the head forwards `R`, every receiver is
served iff all forced senders lie in `insert h R`. -/
theorem relay_serves_iff (F : I → Finset J) (h : J) (R : Finset J) :
    (∀ i, F i ⊆ insert h R) ↔ (univ.biUnion F) ⊆ insert h R := by
  constructor
  · intro hall x hx
    obtain ⟨i, -, hxi⟩ := mem_biUnion.mp hx
    exact hall i hxi
  · intro hU i x hx
    exact hU (mem_biUnion.mpr ⟨i, mem_univ i, hx⟩)

/-! ## The gap witness -/

def wK : Fin 2 → ℕ := ![1, 2]
def wF : Fin 2 → Finset (Fin 3) := ![{0}, {1, 2}]

theorem counting_gap_witness :
    (∀ i, (wF i).card ≤ wK i) ∧
    ¬ (∃ pos : Fin 3 → ℕ, Function.Injective pos ∧ Serves pos wK wF) ∧
    (∀ i, wF i ⊆ insert (0 : Fin 3) {1, 2}) := by
  refine ⟨fun i => by fin_cases i <;> decide, ?_, fun i => by fin_cases i <;> decide⟩
  rw [serves_iff_counting]
  intro h
  have h2 := h 2
  have : forcedBy wK wF 2 = univ := by
    ext j
    simp only [forcedBy, mem_filter, mem_univ, true_and, iff_true]
    fin_cases j
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
  rw [this] at h2
  simp at h2

end CIGAMF.P13.MarlPrefixEDF

#print axioms CIGAMF.P13.MarlPrefixEDF.card_prefix_le
#print axioms CIGAMF.P13.MarlPrefixEDF.serves_necessary
#print axioms CIGAMF.P13.MarlPrefixEDF.edf_serves
#print axioms CIGAMF.P13.MarlPrefixEDF.serves_iff_counting
#print axioms CIGAMF.P13.MarlPrefixEDF.relay_serves_iff
#print axioms CIGAMF.P13.MarlPrefixEDF.counting_gap_witness
