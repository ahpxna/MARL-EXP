import «LeanPaperBParityDecoderV1»

/-!
# Paper B: the formalized identification decoder versus the one the experiment ran

`scripts/EXP_paperB_decoder.py` (`id_decoder_wrong`) decodes the test outcomes as

    named = [j in 1..m-1 that fire];
    guess = named[0] if len(named) == 1 else (m if len(named) == 0 else -1)

and counts `-1` as an error.  The formalized decoder
(`LeanPaperBParityDecoderV1.decodeB`) returns the world the outcome vector points to, and a
DEFAULT world when two or more tests fire.  The two differ exactly on that ambiguous event,
where the experiment always records an error and the formalized decoder may be right.

This module states the experiment's rule in Lean (`pyGuess`, with `none` for `-1`) and proves:

* `pyGuess_some_points` -- when the experiment's rule outputs a world, the outcome vector
  POINTS to it (exactly one firing test names it, or none fires and it is the last world);
* `decodeB_of_pyGuess` -- then the formalized decoder outputs the same world;
* `lean_wrong_imp_py_wrong` -- pathwise, on every outcome vector and at every world, a wrong
  formalized guess implies a wrong experimental guess.

So an error COUNT of the experiment's rule bounds the formalized decoder's error count on the
same samples: the recorded identification errors are a CONSERVATIVE upper bound for the
decoder of `id_correct`, not a measurement of it.  The safe decoder has no ambiguous branch
and the two rules coincide there (`safe_decoder_unsafe` / `safeCode`).
-/

namespace CIGAMF.P13.PaperBDecoderMatch

open CIGAMF.P13.PaperBParityDecoder

variable {m : ℕ}

/-- The tests that fire: queries `j >= 1` whose outcome is `true`. -/
def named (b : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun j => (j : ℕ) ≠ 0 ∧ b j = true

/-- **The experiment's rule**: `some` world, or `none` for the recorded `-1`. -/
noncomputable def pyGuess (hm : 0 < m) (b : Fin m → Bool) : Option (Fin m) :=
  if h1 : (named b).card = 1 then
    some ⟨(Classical.choose (Finset.card_eq_one.mp h1) : Fin m) - 1,
      by have := (Classical.choose (Finset.card_eq_one.mp h1)).isLt; omega⟩
  else if (named b).card = 0 then some ⟨m - 1, by omega⟩ else none

theorem mem_named (b : Fin m → Bool) (j : Fin m) :
    j ∈ named b ↔ (j : ℕ) ≠ 0 ∧ b j = true := by
  simp [named]

/-- **When the experiment outputs a world, the outcome vector points to it.** -/
theorem pyGuess_some_points (hm : 0 < m) (b : Fin m → Bool) (k : Fin m)
    (hk : pyGuess hm b = some k) : Points b k := by
  unfold pyGuess at hk
  split_ifs at hk with h1 h0
  · -- exactly one test fires
    have hspec := Classical.choose_spec (Finset.card_eq_one.mp h1)
    set a := Classical.choose (Finset.card_eq_one.mp h1) with ha
    have hamem : a ∈ named b := by rw [hspec]; exact Finset.mem_singleton_self a
    have ha0 : (a : ℕ) ≠ 0 := ((mem_named b a).mp hamem).1
    have hkv : (k : ℕ) = (a : ℕ) - 1 := by
      have := congrArg (fun o => Option.map Fin.val o) hk
      simp at this
      omega
    intro j hj
    constructor
    · intro hb
      have hjmem : j ∈ named b := (mem_named b j).mpr ⟨hj, hb⟩
      rw [hspec, Finset.mem_singleton] at hjmem
      rw [hjmem, hkv]
      omega
    · intro hjk
      have hja : j = a := by
        apply Fin.ext
        omega
      have := ((mem_named b a).mp hamem).2
      rw [hja]; exact this
  · -- no test fires: the last world
    have hkv : (k : ℕ) = m - 1 := by
      have := congrArg (fun o => Option.map Fin.val o) hk
      simp at this
      omega
    have hempty : named b = ∅ := Finset.card_eq_zero.mp h0
    intro j hj
    constructor
    · intro hb
      have : j ∈ named b := (mem_named b j).mpr ⟨hj, hb⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty j)
    · intro hjk
      have := j.isLt
      omega

/-- **Where the experiment answers, the formalized decoder gives the same answer.** -/
theorem decodeB_of_pyGuess (hm : 0 < m) (b : Fin m → Bool) (k : Fin m)
    (hk : pyGuess hm b = some k) : decodeB hm b = k :=
  decodeB_eq hm b k (pyGuess_some_points hm b k hk)

/-- **Pathwise domination of the errors.** -/
theorem lean_wrong_imp_py_wrong (hm : 0 < m) (b : Fin m → Bool) (w : Fin m)
    (hwrong : decodeB hm b ≠ w) : pyGuess hm b ≠ some w := by
  intro hpy
  exact hwrong (decodeB_of_pyGuess hm b w hpy)

#print axioms pyGuess_some_points
#print axioms decodeB_of_pyGuess
#print axioms lean_wrong_imp_py_wrong

end CIGAMF.P13.PaperBDecoderMatch
