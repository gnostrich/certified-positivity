import Mathlib
import RequestProject.E1
import RequestProject.E2

open scoped BigOperators
open Real

namespace G4

/-!
# G4. Atom enclosures for p = 7 and p = 11

Using `1.9459 < log 7 < 1.9460` (E2) and `2.6457 < √7 < 2.6458` (E1), together with proven
enclosures `2.3978 < log 11 < 2.3980` and `3.3166 < √11 < 3.3167`:

* (a) `0.7354 < (log 7)/√7 < 0.7356`;
* (b) `0.7229 < (log 11)/√11 < 0.7231`;
* (c) `(log 11)/√11 < (log 7)/√7`.
-/

/-- Enclosure `3.3166 < √11 < 3.3167` (by squaring). -/
theorem G4_sqrt11 : (3.3166 : ℝ) < Real.sqrt 11 ∧ Real.sqrt 11 < 3.3167 := by
  constructor
  · rw [show (3.3166 : ℝ) = Real.sqrt (3.3166 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by positivity); norm_num
  · rw [show (3.3167 : ℝ) = Real.sqrt (3.3167 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num); norm_num

/-
Enclosure `2.3978 < log 11 < 2.3980`.  Route: `log 11 = 4·log 2 + log(1 − 5/16)`
with the truncated-series error bound `Real.abs_log_sub_add_sum_range_le` at `x = 5/16`, using
Mathlib's `Real.log_two_gt_d9` / `Real.log_two_lt_d9`.  (An earlier version of this proof
used `native_decide`; replaced 2026-09-14 by a kernel-checkable proof.)
-/
theorem G4_log11 : (2.3978 : ℝ) < Real.log 11 ∧ Real.log 11 < 2.3980 := by
  -- `log 11 = 4 * log 2 + log (11/16)`, and `log (11/16) = log (1 - 5/16)` is bounded by the
  -- truncated Mercator series with an explicit tail bound (kernel-checkable rational arithmetic).
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have key := Real.abs_log_sub_add_sum_range_le (x := (5/16 : ℝ)) (by rw [abs_of_pos] <;> norm_num) 16
  rw [abs_le] at key
  norm_num [Finset.sum_range_succ] at key
  have h11 : Real.log (11/16 : ℝ) = Real.log 11 - 4 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    ring
  rw [h11] at key
  constructor <;> [linarith [key.1]; linarith [key.2]]

/-- (a) The p = 7 atom enclosure. -/
theorem G4_a : (0.7354 : ℝ) < Real.log 7 / Real.sqrt 7 ∧ Real.log 7 / Real.sqrt 7 < 0.7356 := by
  have hs := E1.E1_sqrt7
  have hl := E2.E2_log7
  have hsp : (0 : ℝ) < Real.sqrt 7 := by positivity
  constructor
  · rw [lt_div_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.1]
  · rw [div_lt_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.2]

/-- (b) The p = 11 atom enclosure. -/
theorem G4_b :
    (0.7229 : ℝ) < Real.log 11 / Real.sqrt 11 ∧ Real.log 11 / Real.sqrt 11 < 0.7231 := by
  have hs := G4_sqrt11
  have hl := G4_log11
  have hsp : (0 : ℝ) < Real.sqrt 11 := by positivity
  constructor
  · rw [lt_div_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.1]
  · rw [div_lt_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.2]

/-- (c) The p = 11 atom is smaller than the p = 7 atom. -/
theorem G4_c : Real.log 11 / Real.sqrt 11 < Real.log 7 / Real.sqrt 7 := by
  calc Real.log 11 / Real.sqrt 11 < 0.7231 := G4_b.2
    _ < 0.7354 := by norm_num
    _ < Real.log 7 / Real.sqrt 7 := G4_a.1

end G4