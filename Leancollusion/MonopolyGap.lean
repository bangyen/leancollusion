/-
Theorem 2: the monopoly gap and the markup screen's calibration.

The joint-monopoly outcome is the benchmark the regulator's detection screens
are calibrated against (regulator/screens.py). Here we prove the screen's
[0,1] scale is mathematically well-defined with genuinely separated endpoints.

Textbook reference: Tirole (1988), *The Theory of Industrial Organization*,
Chapter 7 (monopoly vs. oligopoly output).
-/
import Leancollusion.CournotNash
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Leancollusion

/-- Joint-monopoly output (Tirole 1988, Ch. 7: monopoly solution). -/
noncomputable def monopolyQuantity (a b c : ℝ) : ℝ := (a - c) / (2 * b)

/-- Total Nash output across all firms. -/
noncomputable def nashTotalQuantity (n : ℕ) (a b c : ℝ) : ℝ :=
  (n : ℝ) * nashQuantity n a b c

/-- Theorem 2: joint-monopoly output is strictly below Nash output for n ≥ 2.
(Tirole 1988, Ch. 7: monopoly restricts output relative to oligopoly.) -/
theorem monopoly_gap (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn2 : 2 ≤ n) :
    monopolyQuantity a b c < nashTotalQuantity n a b c := by
  have h1 : (0 : ℝ) < a - c := by linarith
  have hN : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have h2b : (0 : ℝ) < 2 * b := by linarith
  have hbN : (0 : ℝ) < b * ((n : ℝ) + 1) := by
    have h1b : (0 : ℝ) < b := hb
    have h2n : (0 : ℝ) < (n : ℝ) + 1 := by
      have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos h1b h2n
  have hM : monopolyQuantity a b c = (a - c) / (2 * b) := rfl
  have hNT : nashTotalQuantity n a b c
      = ((n : ℝ) * (a - c)) / (b * ((n : ℝ) + 1)) := by
    unfold nashTotalQuantity nashQuantity
    rw [← mul_div_assoc]
  rw [hM, hNT, div_lt_div_iff₀ h2b hbN]
  have hdb : (0 : ℝ) < (a - c) * b := mul_pos h1 hb
  nlinarith [mul_pos (sub_pos.mpr hN) hdb]

/-- The monopoly–Nash price gap: the regulator screen's denominator, with its
explicit closed form. -/
theorem price_gap (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn2 : 2 ≤ n) :
    0 < (a - b * monopolyQuantity a b c) - (a - b * nashTotalQuantity n a b c)
      ∧ (a - b * monopolyQuantity a b c) - (a - b * nashTotalQuantity n a b c)
        = (a - c) * ((n : ℝ) - 1) / (2 * ((n : ℝ) + 1)) := by
  have hgap := monopoly_gap n a b c hb hca hn2
  have hM : monopolyQuantity a b c = (a - c) / (2 * b) := rfl
  have hNT : nashTotalQuantity n a b c
      = ((n : ℝ) * (a - c)) / (b * ((n : ℝ) + 1)) := by
    unfold nashTotalQuantity nashQuantity
    rw [← mul_div_assoc]
  constructor
  · have heq : (a - b * monopolyQuantity a b c) - (a - b * nashTotalQuantity n a b c)
        = b * (nashTotalQuantity n a b c - monopolyQuantity a b c) := by ring
    rw [heq]
    exact mul_pos hb (sub_pos.mpr hgap)
  · rw [hM, hNT]
    have h2b : (2 : ℝ) * b ≠ 0 := ne_of_gt (by linarith)
    have hbN : b * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by
      have h1b : (0 : ℝ) < b := hb
      have h2n : (0 : ℝ) < (n : ℝ) + 1 := by
        have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact mul_pos h1b h2n)
    have hN1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by
      have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
    field_simp
    ring

/-- The markup screen: mean price position between Nash (0) and monopoly (1).
(regulator/screens.py in the regulator repository.) -/
noncomputable def markupScreen (pbar pN pM : ℝ) : ℝ := (pbar - pN) / (pM - pN)

/-- S(Nash) = 0. -/
theorem screen_nash_zero (n : ℕ) (a b c : ℝ) :
    markupScreen (a - b * nashTotalQuantity n a b c)
      (a - b * nashTotalQuantity n a b c) (a - b * monopolyQuantity a b c)
      = 0 := by
  unfold markupScreen
  rw [sub_self, zero_div]

/-- S(monopoly) = 1, with strictly positive denominator. -/
theorem screen_monopoly_one (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn2 : 2 ≤ n) :
    markupScreen (a - b * monopolyQuantity a b c)
      (a - b * nashTotalQuantity n a b c) (a - b * monopolyQuantity a b c)
      = 1 := by
  have hgap := price_gap n a b c hb hca hn2
  unfold markupScreen
  exact div_self (ne_of_gt hgap.1)

end Leancollusion
