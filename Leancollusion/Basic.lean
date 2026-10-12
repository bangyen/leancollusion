/-
Cournot game model: n-firm linear Cournot competition with symmetric constant
marginal costs.

Textbook reference: Tirole (1988), *The Theory of Industrial Organization*,
Chapter 7.1 (Cournot competition). Equilibrium notions are reused from
Econlib (`Econlib.GameTheory.StrategicGame.IsNash`), not redefined here.
-/
import Econlib.GameTheory.Strategic.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Leancollusion

/-- The n-firm linear Cournot game: each firm chooses a nonnegative quantity,
inverse demand is P(Q) = a − bQ, and every firm has constant marginal cost c.
(Tirole 1988, Ch. 7.1.) -/
def cournotGame (n : ℕ) (a b c : ℝ) (hn : 0 < n) :
    Econlib.GameTheory.StrategicGame where
  Player := Fin n
  Action := fun _ => { q : ℝ // 0 ≤ q }
  payoff := fun i q => (q i).val * (a - b * (∑ j, (q j).val) - c)
  instInhabitedPlayer := ⟨⟨0, hn⟩⟩
  instDecidableEqPlayer := inferInstance
  instInhabitedAction := fun _ => ⟨⟨0, le_refl 0⟩⟩

/-- Firm i's profit as a function of its own quantity `x`, holding rivals fixed. -/
def ownProfit (n : ℕ) (a b c : ℝ) (q : Fin n → { q : ℝ // 0 ≤ q }) (i : Fin n)
    (x : ℝ) : ℝ :=
  x * (a - c - b * ((∑ j ∈ Finset.univ.erase i, (q j).val) + x))

/-- Payoff at a profile equals own profit evaluated at the firm's own quantity. -/
theorem payoff_eq_ownProfit (n : ℕ) (a b c : ℝ) (hn : 0 < n)
    (q : Fin n → { q : ℝ // 0 ≤ q }) (i : Fin n) :
    (cournotGame n a b c hn).payoff i q = ownProfit n a b c q i (q i).val := by
  have hsum : ∑ j, (q j).val
      = (∑ j ∈ Finset.univ.erase i, (q j).val) + (q i).val := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
  change (q i).val * (a - b * (∑ j, (q j).val) - c)
    = (q i).val * (a - c - b * ((∑ j ∈ Finset.univ.erase i, (q j).val) + (q i).val))
  rw [hsum]
  ring

/-- Payoff after a unilateral deviation equals own profit at the new quantity. -/
theorem payoff_update_eq (n : ℕ) (a b c : ℝ) (hn : 0 < n)
    (q : Fin n → { q : ℝ // 0 ≤ q }) (i : Fin n) (xi : { q : ℝ // 0 ≤ q }) :
    (cournotGame n a b c hn).payoff i (Function.update q i xi)
      = ownProfit n a b c q i xi.val := by
  have hsum : ∑ j, ((Function.update q i xi) j).val
      = xi.val + ∑ j ∈ Finset.univ.erase i, (q j).val := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · rw [Function.update_self]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Function.update_of_ne hji]
  change (Function.update q i xi i).val * (a - b * (∑ j, ((Function.update q i xi) j).val) - c)
    = xi.val * (a - c - b * ((∑ j ∈ Finset.univ.erase i, (q j).val) + xi.val))
  rw [hsum, Function.update_self]
  ring

/-- The concave-quadratic profit `K·x − b·x²` is maximized over `x ≥ 0` at
`max 0 (K/(2b))`. (Completing the square; cf. Tirole 1988, Ch. 7.1.) -/
theorem quad_max (b : ℝ) (hb : 0 < b) (K x : ℝ) (hx : 0 ≤ x) :
    K * x - b * x ^ 2
      ≤ K * max 0 (K / (2 * b)) - b * (max 0 (K / (2 * b))) ^ 2 := by
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  by_cases hK : K ≤ 0
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hK (le_of_lt hb2))]
    have e1 : K * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK hx
    have e2 : (0 : ℝ) ≤ b * x ^ 2 := by positivity
    linarith
  · rw [not_le] at hK
    rw [max_eq_right (le_of_lt (div_pos hK hb2))]
    have h2bne : (2 : ℝ) * b ≠ 0 := ne_of_gt hb2
    have hid : K * (K / (2 * b)) - b * (K / (2 * b)) ^ 2 - (K * x - b * x ^ 2)
        = b * (x - K / (2 * b)) ^ 2 := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ b * (x - K / (2 * b)) ^ 2 :=
      mul_nonneg (le_of_lt hb) (sq_nonneg _)
    linarith

/-- The maximizer is unique. -/
theorem quad_max_unique (b : ℝ) (hb : 0 < b) (K x : ℝ) (hx : 0 ≤ x)
    (h : K * max 0 (K / (2 * b)) - b * (max 0 (K / (2 * b))) ^ 2
      ≤ K * x - b * x ^ 2) :
    x = max 0 (K / (2 * b)) := by
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  by_cases hK : K ≤ 0
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hK (le_of_lt hb2))] at h ⊢
    -- From h : 0 ≤ K*x − b*x² together with K*x − b*x² ≤ 0, the product
    -- x*(K − b*x) vanishes; since K − b*x ≤ 0 and x ≥ 0, x = 0.
    have hle : K * x - b * x ^ 2 ≤ 0 := by
      have e1 : K * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK hx
      have e2 : (0 : ℝ) ≤ b * x ^ 2 := by positivity
      linarith
    have heq : x * (K - b * x) = 0 := by
      have hid : x * (K - b * x) = K * x - b * x ^ 2 := by ring
      linarith
    have hKbx : K - b * x ≤ 0 := by
      have e2 : (0 : ℝ) ≤ b * x := by positivity
      linarith
    rcases mul_eq_zero.mp heq with hx0 | hKbx0
    · exact hx0
    · -- From K − b*x = 0 and K ≤ 0: b*x ≤ 0, but b*x ≥ 0, so b*x = 0 and x = 0.
      have hbx_eq : b * x = K := by linarith
      have h1 : b * x ≤ 0 := by linarith
      have h2 : (0 : ℝ) ≤ b * x := by positivity
      have h3 : b * x = 0 := le_antisymm h1 h2
      rcases eq_or_ne x 0 with rfl | hne
      · rfl
      · exfalso
        exact mul_ne_zero (ne_of_gt hb) hne h3
  · rw [not_le] at hK
    rw [max_eq_right (le_of_lt (div_pos hK hb2))] at h ⊢
    have h2bne : (2 : ℝ) * b ≠ 0 := ne_of_gt hb2
    have hid : K * (K / (2 * b)) - b * (K / (2 * b)) ^ 2 - (K * x - b * x ^ 2)
        = b * (x - K / (2 * b)) ^ 2 := by
      field_simp
      ring
    have hle : b * (x - K / (2 * b)) ^ 2 ≤ 0 := by linarith
    have hsq : (x - K / (2 * b)) ^ 2 ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      have hpos := mul_pos hb hcon
      linarith
    have hz : x - K / (2 * b) = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    linarith

end Leancollusion
