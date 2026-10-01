import Mathlib
example (a b : ℝ) (hb : b ≠ 0) (h5b' : b * 5 - a ≠ 0) :
    2 * b * (3 * b - a) / (5 * b - a) = (4 * b - a) / 3 - (a - b) / 6 * (2 * (a - 2 * b) / (5 * b - a)) := by
  field_simp
  ring
example (a b : ℝ) (hb : b ≠ 0) (h5b' : b * 5 - a ≠ 0) :
    2 * b * (3 * b - a) / (5 * b - a) = (a - b) * (3 * b - a) / (2 * b) + (3 * b - a) ^ 2 / (6 * b)
      - (3 * b - a) ^ 2 / (6 * b) * (2 * (a - 2 * b) / (5 * b - a)) := by
  field_simp
  ring
example (a b : ℝ) (hab : a - b ≠ 0) (h17 : b * 17 - a * 5 ≠ 0) :
    4 * b * (3 * b - a) / (17 * b - 5 * a) = (4 * b - a) / 3 - (a - b) / 6
      * (2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a))) := by
  field_simp
  ring
example (a b : ℝ) (hab : a - b ≠ 0) (h17 : b * 17 - a * 5 ≠ 0) (hq : a * b * 15 - a ^ 2 * 3 - b ^ 2 * 16 ≠ 0) :
    4 * b * (3 * b - a) / (17 * b - 5 * a)
      = 2 * a * (a - b) * (3 * b - a) / (3 * (15 * a * b - 3 * a * a - 16 * b * b))
        - (a - b) * (3 * b - a) ^ 2 / (3 * (15 * a * b - 3 * a * a - 16 * b * b))
          * (2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a))) := by
  field_simp
  ring
