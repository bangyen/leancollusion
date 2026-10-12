/-
Theorem 3: grim-trigger collusion sustainability in the linear Cournot model.

When is the joint-monopoly (collusive) outcome sustainable as a subgame-perfect
equilibrium of the infinitely repeated Cournot game, supported by Nash-reversion
grim trigger? The one-shot deviation principle (Friedman 1971; Tirole 1988,
Ch. 6.3.2) reduces this to the incentive constraint

  (1 − δ)·π^D + δ·π^N ≤ π^C,

where π^C is the collusive per-period payoff, π^D the optimal one-shot
deviation payoff, and π^N the Nash punishment payoff. We prove this holds iff
the discount factor δ clears an explicit critical threshold
δ* = (n+1)²/(n²+6n+1), computed in closed form from the Cournot parameters
(a, b, c, n). For duopoly this is the textbook 9/17.

Textbook references: Friedman, J. W. (1971), "A Non-Cooperative Equilibrium
for Supergames", *Review of Economic Studies*; Tirole (1988), *The Theory of
Industrial Organization*, Ch. 6.3.2 (repeated Cournot); Mas-Colell, Whinston &
Green (1995), Ch. 12.G (repeated games, one-shot deviation principle).

Note on scope and the Econlib bridge: Econlib's
`Econlib.GameTheory.Repeated.GrimTrigger.grimTrigger_isSubgamePerfectEquilibrium`
proves grim trigger is a subgame-perfect equilibrium under a calibration
hypothesis `hcalib` that is *exactly* the incentive constraint above — but its
`RepeatedGame` requires a `FiniteStrategicGame` stage game, while our Cournot
stage game has the continuous action space `{q : ℝ // 0 ≤ q}`. We therefore
prove the δ* threshold directly for the continuous Cournot model (the full
content of the calibration), and `grimTriggerCalibrated` below *is* Econlib's
`hcalib` instantiated at the Cournot stage game. Lifting to Econlib's full
`IsSubgamePerfectEquilibrium` would require a finite-action discretization of
the stage game, which is out of scope.
-/
import Leancollusion.MonopolyGap
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Leancollusion

/-- Per-firm collusive quantity: joint monopoly split evenly.
(Tirole 1988, Ch. 6.3.2.) -/
noncomputable def collusionQuantity (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) / (2 * b * (n : ℝ))

theorem collusionQuantity_nonneg (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn : 0 < n) :
    0 ≤ collusionQuantity n a b c := by
  unfold collusionQuantity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact div_nonneg (by linarith)
    (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hb)) (le_of_lt hnR))

/-- The collusive profile: every firm produces the collusive quantity. -/
noncomputable def collusionProfile (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn : 0 < n) :
    Fin n → { q : ℝ // 0 ≤ q } :=
  fun _ => ⟨collusionQuantity n a b c, collusionQuantity_nonneg n a b c hb hca hn⟩

@[simp]
theorem collusionProfile_val (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn : 0 < n) (i : Fin n) :
    ((collusionProfile n a b c hb hca hn) i).val = collusionQuantity n a b c := rfl

/-- Rivals' total output at the collusive profile. -/
theorem collusionProfile_erase_sum (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, ((collusionProfile n a b c hb hca hn) j).val
      = ((n : ℝ) - 1) * collusionQuantity n a b c := by
  have h1 : ∑ j ∈ Finset.univ.erase i, ((collusionProfile n a b c hb hca hn) j).val
      = ∑ j ∈ Finset.univ.erase i, collusionQuantity n a b c :=
    Finset.sum_congr rfl (fun j _ => collusionProfile_val n a b c hb hca hn j)
  rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h2 : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
    rw [Nat.cast_add, Nat.cast_one] at h2
    linarith
  rw [hcast]

/-- Per-firm collusive per-period payoff: π^C = (a−c)²/(4bn).
(Tirole 1988, Ch. 6.3.2.) -/
noncomputable def collusionProfit (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) ^ 2 / (4 * b * (n : ℝ))

/-- Per-firm Nash per-period payoff: π^N = (a−c)²/(b(n+1)²).
(Tirole 1988, Ch. 7.1.) -/
noncomputable def nashProfit (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) ^ 2 / (b * ((n : ℝ) + 1) ^ 2)

/-- The optimal one-shot deviation quantity against colluding rivals:
q^D = (a−c)(n+1)/(4bn). (Tirole 1988, Ch. 6.3.2.) -/
noncomputable def deviationQuantity (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) * ((n : ℝ) + 1) / (4 * b * (n : ℝ))

/-- The optimal one-shot deviation payoff: π^D = (a−c)²(n+1)²/(16bn²).
(Tirole 1988, Ch. 6.3.2.) -/
noncomputable def deviationProfit (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) ^ 2 * ((n : ℝ) + 1) ^ 2 / (16 * b * (n : ℝ) ^ 2)

/-- The critical discount factor: grim-trigger collusion is sustainable iff
δ ≥ δ*. (Friedman 1971; Tirole 1988, Ch. 6.3.2.) -/
noncomputable def criticalDiscount (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 / ((n : ℝ) ^ 2 + 6 * (n : ℝ) + 1)

/-- The collusive payoff closed form, from the stage-game payoff. -/
theorem collusionProfit_eq (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) :
    (cournotGame n a b c hn).payoff i (collusionProfile n a b c hb hca hn)
      = collusionProfit n a b c := by
  rw [payoff_eq_ownProfit]
  simp only [collusionProfile_val]
  have hS := collusionProfile_erase_sum n a b c hn hb hca i
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2bn : (2 : ℝ) * b * (n : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hb) hnR)
  unfold ownProfit collusionProfit
  rw [hS]
  unfold collusionQuantity
  field_simp
  ring

/-- The Nash payoff closed form, from the stage-game payoff and Theorem 1. -/
theorem nashProfit_eq (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) :
    (cournotGame n a b c hn).payoff i (nashProfile n a b c hb hca)
      = nashProfit n a b c := by
  rw [payoff_eq_ownProfit]
  simp only [nashProfile_val]
  have hS := nashProfile_erase_sum n a b c hn hb hca i
  have hNp1 : b * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by
    have h1 : (0 : ℝ) < b := hb
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by
      have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos h1 h2)
  unfold ownProfit nashProfit
  rw [hS]
  unfold nashQuantity
  field_simp
  ring

/-- Against colluding rivals, firm i's profit as a function of its own
quantity is the concave quadratic K·x − b·x² with
K = (a−c)(n+1)/(2n). -/
theorem deviationK (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b) (hca : c < a)
    (i : Fin n) (x : ℝ) :
    ownProfit n a b c (collusionProfile n a b c hb hca hn) i x
      = ((a - c) * ((n : ℝ) + 1) / (2 * (n : ℝ))) * x - b * x ^ 2 := by
  have hS := collusionProfile_erase_sum n a b c hn hb hca i
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2bn : (2 : ℝ) * b * (n : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hb) hnR)
  have h2n : (2 : ℝ) * (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  unfold ownProfit
  rw [hS]
  unfold collusionQuantity
  field_simp
  ring

/-- The best-response constant is positive (so the maximizer is interior). -/
theorem deviationK_pos (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) :
    0 < (a - c) * ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < a - c := by linarith
  have h2 : (0:ℝ) < (n:ℝ) + 1 := by
    have hN : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have h3 : (0:ℝ) < 2 * (n:ℝ) := by linarith
  exact div_pos (mul_pos h1 h2) h3

theorem deviationQuantity_nonneg (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn : 0 < n) :
    0 ≤ deviationQuantity n a b c := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) ≤ a - c := by linarith
  have h2 : (0:ℝ) ≤ (n:ℝ) + 1 := by
    have hN : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have h3 : (0:ℝ) ≤ 4 * b * (n:ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hb)) (le_of_lt hnR)
  unfold deviationQuantity
  exact div_nonneg (mul_nonneg h1 h2) h3

/-- The deviation quantity is the interior maximizer K/(2b). -/
theorem deviationQuantity_eq (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) :
    deviationQuantity n a b c
      = max 0 (((a - c) * ((n : ℝ) + 1) / (2 * (n : ℝ))) / (2 * b)) := by
  have h2b : (0 : ℝ) < 2 * b := by linarith
  have hK := deviationK_pos n a b c hn hb hca
  rw [max_eq_right (le_of_lt (div_pos hK h2b))]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2n : (2 : ℝ) * (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h4bn : (4 : ℝ) * b * (n : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hb) hnR)
  unfold deviationQuantity
  field_simp
  ring

/-- The deviation quantity is the unique best response to colluding rivals
(strict concavity of profits; cf. Tirole 1988, Ch. 6.3.2). -/
theorem deviation_bestResponse (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) (x : ℝ) (hx : 0 ≤ x) :
    ownProfit n a b c (collusionProfile n a b c hb hca hn) i x
      ≤ ownProfit n a b c (collusionProfile n a b c hb hca hn) i
          (deviationQuantity n a b c) := by
  have hK := deviationK n a b c hn hb hca i
  rw [hK x, hK (deviationQuantity n a b c)]
  have hxD : (0 : ℝ) ≤ deviationQuantity n a b c :=
    deviationQuantity_nonneg n a b c hb hca hn
  have hquad := quad_max b hb ((a - c) * ((n : ℝ) + 1) / (2 * (n : ℝ))) x hx
  rw [← deviationQuantity_eq n a b c hn hb hca] at hquad
  exact hquad

/-- The deviation payoff closed form: π^D = K²/(4b) at the best response. -/
theorem deviationProfit_eq (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) :
    ownProfit n a b c (collusionProfile n a b c hb hca hn) i
        (deviationQuantity n a b c)
      = deviationProfit n a b c := by
  rw [deviationK n a b c hn hb hca i]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h2n : (2 : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hn0
  have h4bn : (4 : ℝ) * b * (n : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb0) hn0
  have h16 : (16 : ℝ) * b * (n : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb0) (pow_ne_zero 2 hn0)
  unfold deviationQuantity deviationProfit
  field_simp
  ring

/-- Payoff ordering: Nash < collusion < deviation, for n ≥ 2.
(Friedman 1971: the deviation is tempting and the punishment hurts.) -/
theorem payoff_ordering (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn2 : 2 ≤ n) :
    nashProfit n a b c < collusionProfit n a b c
      ∧ collusionProfit n a b c < deviationProfit n a b c := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hA : (0 : ℝ) < (a - c) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hden1 : (0 : ℝ) < b * ((n : ℝ) + 1) ^ 2 := by
    apply mul_pos hb
    exact sq_pos_of_ne_zero (show ((n : ℝ) + 1) ≠ 0 by
      have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  have hden2 : (0 : ℝ) < 4 * b * (n : ℝ) :=
    mul_pos (mul_pos (by norm_num) hb) hn0
  have hden3 : (0 : ℝ) < 16 * b * (n : ℝ) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hb) (sq_pos_of_ne_zero (ne_of_gt hn0))
  -- Both inequalities reduce to 4n < (n+1)², i.e. 0 < (n−1)².
  have hkey : (4 : ℝ) * (n : ℝ) < ((n : ℝ) + 1) ^ 2 := by
    have hsq : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 :=
      sq_pos_of_ne_zero (by linarith)
    nlinarith [hsq]
  constructor
  · unfold nashProfit collusionProfit
    rw [div_lt_div_iff₀ hden1 hden2]
    have hbn : (4 : ℝ) * b * (n : ℝ) < b * ((n : ℝ) + 1) ^ 2 := by
      have h2 := mul_lt_mul_of_pos_left hkey hb
      linarith
    exact mul_lt_mul_of_pos_left hbn hA
  · unfold collusionProfit deviationProfit
    rw [div_lt_div_iff₀ hden2 hden3]
    have hbn : (16 : ℝ) * b * (n : ℝ) ^ 2
        < ((n : ℝ) + 1) ^ 2 * (4 * b * (n : ℝ)) := by
      have h2 := mul_lt_mul_of_pos_right hkey hden2
      linarith
    have h3 := mul_lt_mul_of_pos_left hbn hA
    calc (a - c) ^ 2 * (16 * b * (n : ℝ) ^ 2)
        < (a - c) ^ 2 * (((n : ℝ) + 1) ^ 2 * (4 * b * (n : ℝ))) := h3
      _ = (a - c) ^ 2 * ((n : ℝ) + 1) ^ 2 * (4 * b * (n : ℝ)) := by ring

/-- The one-shot deviation principle in payoff space: the incentive constraint
`(1−δ)·π^D + δ·π^N ≤ π^C` holds iff δ clears the threshold
(π^D − π^C)/(π^D − π^N). This is pure algebra in the payoffs — no bounds on δ
are needed. (Friedman 1971; Tirole 1988, Ch. 6.3.2.) -/
theorem oneShotDeviation_iff {πC πD πN δ : ℝ}
    (hDN : πN < πD) :
    (1 - δ) * πD + δ * πN ≤ πC ↔ (πD - πC) / (πD - πN) ≤ δ := by
  have hpos : (0 : ℝ) < πD - πN := by linarith
  constructor
  · intro h
    rw [div_le_iff₀ hpos]
    linarith
  · intro h
    rw [div_le_iff₀ hpos] at h
    linarith

/-- The critical discount factor in closed form: δ* = (n+1)²/(n²+6n+1).
For duopoly (n = 2) this is the textbook 9/17 (Tirole 1988, Ch. 6.3.2). -/
theorem criticalDiscount_eq (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (hn2 : 2 ≤ n) :
    (deviationProfit n a b c - collusionProfit n a b c)
      / (deviationProfit n a b c - nashProfit n a b c)
      = criticalDiscount n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hA : (0 : ℝ) < (a - c) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hNp1 : (0 : ℝ) < (n : ℝ) + 1 := by
    have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have d1 : (16 : ℝ) * b * (n : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb0) (pow_ne_zero 2 hn0')
  have d2 : (4 : ℝ) * b * (n : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hb0) hn0'
  have d3 : b * ((n : ℝ) + 1) ^ 2 ≠ 0 :=
    mul_ne_zero hb0 (pow_ne_zero 2 (ne_of_gt hNp1))
  -- Numerator: π^D − π^C = (a−c)²(n−1)²/(16bn²).
  have hnum : deviationProfit n a b c - collusionProfit n a b c
      = (a - c) ^ 2 * ((n : ℝ) - 1) ^ 2 / (16 * b * (n : ℝ) ^ 2) := by
    unfold deviationProfit collusionProfit
    field_simp
    ring
  -- Denominator: π^D − π^N = (a−c)²(n−1)²(n²+6n+1)/(16bn²(n+1)²).
  have hden : deviationProfit n a b c - nashProfit n a b c
      = (a - c) ^ 2 * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) ^ 2 + 6 * (n : ℝ) + 1)
        / (16 * b * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
    unfold deviationProfit nashProfit
    field_simp
    ring
  rw [hnum, hden]
  have hX : (a - c) ^ 2 * ((n : ℝ) - 1) ^ 2 / (16 * b * (n : ℝ) ^ 2) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (ne_of_gt hA)
        (pow_ne_zero 2 (by linarith))
    · exact d1
  have hfac : (a - c) ^ 2 * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) ^ 2 + 6 * (n : ℝ) + 1)
        / (16 * b * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)
      = ((a - c) ^ 2 * ((n : ℝ) - 1) ^ 2 / (16 * b * (n : ℝ) ^ 2))
        * (((n : ℝ) ^ 2 + 6 * (n : ℝ) + 1) / ((n : ℝ) + 1) ^ 2) := by
    field_simp
  rw [hfac, div_mul_eq_div_div, div_self hX, one_div_div]
  rfl

/-- Econlib's grim-trigger calibration hypothesis (`hcalib` in
`Econlib.GameTheory.Repeated.GrimTrigger.grimTrigger_isSubgamePerfectEquilibrium`),
instantiated at the Cournot stage game with the collusive profile as
`cooperate` and the Nash profile as `punish`. -/
def grimTriggerCalibrated (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (δ : ℝ) : Prop :=
  ∀ (i : Fin n) (xi : { q : ℝ // 0 ≤ q }),
    (1 - δ) * (cournotGame n a b c hn).payoff i
        (Function.update (collusionProfile n a b c hb hca hn) i xi)
      + δ * (cournotGame n a b c hn).payoff i (nashProfile n a b c hb hca)
      ≤ (cournotGame n a b c hn).payoff i (collusionProfile n a b c hb hca hn)

/-- **Theorem 3 (grim-trigger sustainability):** the calibration — and hence
Nash-reversion grim trigger as a subgame-perfect equilibrium of the infinitely
repeated Cournot game — holds iff the discount factor clears the critical
threshold δ* = (n+1)²/(n²+6n+1). (Friedman 1971; Tirole 1988, Ch. 6.3.2.) -/
theorem grimTrigger_sustainability (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (hn2 : 2 ≤ n) (δ : ℝ) (hδ1 : δ < 1) :
    grimTriggerCalibrated n a b c hn hb hca δ ↔ criticalDiscount n ≤ δ := by
  have hord := payoff_ordering n a b c hb hca hn2
  have hC := collusionProfit_eq n a b c hn hb hca
  have hN := nashProfit_eq n a b c hn hb hca
  have hD := deviationProfit_eq n a b c hn hb hca
  have hBR := deviation_bestResponse n a b c hn hb hca
  have hiff : grimTriggerCalibrated n a b c hn hb hca δ
      ↔ (1 - δ) * deviationProfit n a b c + δ * nashProfit n a b c
          ≤ collusionProfit n a b c := by
    unfold grimTriggerCalibrated
    constructor
    · intro h
      have hxi : (0 : ℝ) ≤ deviationQuantity n a b c :=
        deviationQuantity_nonneg n a b c hb hca hn
      have hinst := h ⟨0, hn⟩ ⟨deviationQuantity n a b c, hxi⟩
      have hval : ((⟨deviationQuantity n a b c, hxi⟩ :
          { q : ℝ // 0 ≤ q }).val) = deviationQuantity n a b c := rfl
      rw [payoff_update_eq, hval, hD ⟨0, hn⟩, hN ⟨0, hn⟩, hC ⟨0, hn⟩] at hinst
      exact hinst
    · intro h i xi
      have hle : (cournotGame n a b c hn).payoff i
          (Function.update (collusionProfile n a b c hb hca hn) i xi)
          ≤ deviationProfit n a b c := by
        rw [payoff_update_eq]
        have h2 := hBR i xi.val xi.property
        rw [hD i] at h2
        exact h2
      have h1mδ : (0 : ℝ) ≤ 1 - δ := by linarith
      calc (1 - δ) * (cournotGame n a b c hn).payoff i
              (Function.update (collusionProfile n a b c hb hca hn) i xi)
            + δ * (cournotGame n a b c hn).payoff i (nashProfile n a b c hb hca)
          ≤ (1 - δ) * deviationProfit n a b c + δ * nashProfit n a b c := by
            rw [hN i]
            exact add_le_add (mul_le_mul_of_nonneg_left hle h1mδ) le_rfl
        _ ≤ collusionProfit n a b c := h
        _ = (cournotGame n a b c hn).payoff i
              (collusionProfile n a b c hb hca hn) := by rw [hC i]
  rw [hiff, ← criticalDiscount_eq n a b c hb hca hn2]
  exact oneShotDeviation_iff (by linarith [hord.1, hord.2])

end Leancollusion
