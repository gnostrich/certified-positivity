import Mathlib

open scoped BigOperators
open Real

namespace E2

/-!
# E2. Enclosure toolkit: logarithms

Explicit rational enclosures of `log 2, log 3, log 5, log 7`.
-/

theorem E2_log2 : (0.6931 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6932 := by
  exact ⟨ Real.log_two_gt_d9.trans_le' <| by norm_num, Real.log_two_lt_d9.trans_le <| by norm_num ⟩

theorem E2_log3 : (1.0986 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0987 := by
  -- `log 3 = 2 * log 2 + log (3/4)`, and `log (3/4) = log (1 - 1/4)` is bounded by the
  -- truncated Mercator series with an explicit tail bound (kernel-checkable rational arithmetic).
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have key := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by rw [abs_of_pos] <;> norm_num) 12
  rw [abs_le] at key
  norm_num [Finset.sum_range_succ] at key
  have h34 : Real.log (3/4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  rw [h34] at key
  constructor <;> [linarith [key.1]; linarith [key.2]]

theorem E2_log5 : (1.6094 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.6095 := by
  -- `log 5 = 2 * log 2 + log (5/4)`, and `log (5/4) = log (1 - (-1/4))`.
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have key := Real.abs_log_sub_add_sum_range_le (x := (-1/4 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 12
  rw [abs_le] at key
  norm_num [Finset.sum_range_succ] at key
  have h54 : Real.log (5/4 : ℝ) = Real.log 5 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  rw [h54] at key
  constructor <;> [linarith [key.1]; linarith [key.2]]

theorem E2_log7 : (1.9459 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.9460 := by
  -- `log 7 = 3 * log 2 + log (7/8)`, and `log (7/8) = log (1 - 1/8)`.
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have key := Real.abs_log_sub_add_sum_range_le (x := (1/8 : ℝ)) (by rw [abs_of_pos] <;> norm_num) 8
  rw [abs_le] at key
  norm_num [Finset.sum_range_succ] at key
  have h78 : Real.log (7/8 : ℝ) = Real.log 7 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    ring
  rw [h78] at key
  constructor <;> [linarith [key.1]; linarith [key.2]]

end E2