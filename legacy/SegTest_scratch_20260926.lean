import Mathlib
theorem seg_id1 {Q E QW α β : ℝ} (hQ : Q ≠ 0) (h : QW = α * Q - β * E) :
    QW / Q = α - β * (E / Q) := by
  rw [h]; field_simp
theorem seg_id2 {Q E QW A B Dd : ℝ} (hQ : Q ≠ 0) (hD : Dd ≠ 0) (h : QW * Dd = A * Q - B * E) :
    QW / Q = A / Dd - B / Dd * (E / Q) := by
  rw [div_eq_iff hQ, sub_mul, div_mul_eq_mul_div, div_mul_div_comm, div_mul_eq_mul_div,
    eq_div_iff hD] at *
  field_simp
  linear_combination h
theorem seg_id2' {Q E QW A B Dd : ℝ} (hQ : Q ≠ 0) (hD : Dd ≠ 0) (h : QW * Dd = A * Q - B * E) :
    QW / Q = A / Dd - B / Dd * (E / Q) := by
  have e : A / Dd - B / Dd * (E / Q) = (A * Q - B * E) / (Dd * Q) := by field_simp
  rw [e, div_eq_div_iff hQ (mul_ne_zero hD hQ)]
  linear_combination Q * h
theorem const_id {Q QW N Dn : ℝ} (hQ : Q ≠ 0) (hD : Dn ≠ 0) (h : QW * Dn = N * Q) : QW / Q = N / Dn := by
  rw [div_eq_div_iff hQ hD]; exact h
