/-
Theorem 1: the symmetric linear-Cournot Nash equilibrium.

Textbook reference: Tirole (1988), *The Theory of Industrial Organization*,
Chapter 7.1 (Cournot competition: equilibrium quantities and uniqueness via
strict concavity of profits).
-/
import Leancollusion.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Leancollusion

/-- The symmetric Cournot-Nash quantity (Tirole 1988, Ch. 7.1). -/
noncomputable def nashQuantity (n : ℕ) (a b c : ℝ) : ℝ :=
  (a - c) / (b * ((n : ℝ) + 1))

theorem nashQuantity_pos (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a) :
    0 < nashQuantity n a b c := by
  unfold nashQuantity
  apply div_pos
  · linarith
  · have h1 : (0 : ℝ) < b := hb
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by
      have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos h1 h2

theorem nashQuantity_nonneg (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a) :
    0 ≤ nashQuantity n a b c :=
  le_of_lt (nashQuantity_pos n a b c hb hca)

/-- The symmetric candidate profile. -/
noncomputable def nashProfile (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a) :
    Fin n → { q : ℝ // 0 ≤ q } :=
  fun _ => ⟨nashQuantity n a b c, nashQuantity_nonneg n a b c hb hca⟩

@[simp]
theorem nashProfile_val (n : ℕ) (a b c : ℝ) (hb : 0 < b) (hca : c < a)
    (i : Fin n) :
    ((nashProfile n a b c hb hca) i).val = nashQuantity n a b c := rfl

/-- Rivals' total output at the symmetric candidate. -/
theorem nashProfile_erase_sum (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, ((nashProfile n a b c hb hca) j).val
      = ((n : ℝ) - 1) * nashQuantity n a b c := by
  have h1 : ∑ j ∈ Finset.univ.erase i, ((nashProfile n a b c hb hca) j).val
      = ∑ j ∈ Finset.univ.erase i, nashQuantity n a b c :=
    Finset.sum_congr rfl (fun j _ => nashProfile_val n a b c hb hca j)
  rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h2 : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
    rw [Nat.cast_add, Nat.cast_one] at h2
    linarith
  rw [hcast]

/-- At the candidate, each firm's best-response formula returns the candidate
quantity (first-order condition of the concave profit). -/
theorem nashProfile_bestResponse (n : ℕ) (a b c : ℝ) (hb : 0 < b) :
    (a - c - b * (((n : ℝ) - 1) * nashQuantity n a b c)) / (2 * b)
      = nashQuantity n a b c := by
  unfold nashQuantity
  have h2bpos : (0 : ℝ) < 2 * b := by linarith
  have h2b : (2 : ℝ) * b ≠ 0 := ne_of_gt h2bpos
  have hbN : b * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by
    have h1 : (0 : ℝ) < b := hb
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by
      have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos h1 h2)
  field_simp
  ring

/-- Theorem 1 (existence): the symmetric profile is a Nash equilibrium.
(Tirole 1988, Ch. 7.1, Cournot-Nash equilibrium.) -/
theorem cournotNash_symmetric (n : ℕ) (a b c : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hca : c < a) :
    (cournotGame n a b c hn).IsNash (nashProfile n a b c hb hca) := by
  rw [Econlib.GameTheory.StrategicGame.isNash_iff]
  intro i xi
  have hS := nashProfile_erase_sum n a b c hn hb hca i
  have hKval := nashProfile_bestResponse n a b c hb
  have hqpos := nashQuantity_pos n a b c hb hca
  have hquad := quad_max b hb
    (a - c - b * (((n : ℝ) - 1) * nashQuantity n a b c)) xi.val xi.property
  rw [show max 0 ((a - c - b * (((n : ℝ) - 1) * nashQuantity n a b c)) / (2 * b))
      = nashQuantity n a b c from by
    rw [hKval]
    exact max_eq_right (le_of_lt hqpos)] at hquad
  rw [payoff_eq_ownProfit, payoff_update_eq]
  simp only [nashProfile_val]
  have e1 : ownProfit n a b c (nashProfile n a b c hb hca) i (nashQuantity n a b c)
      = (a - c - b * (((n : ℝ) - 1) * nashQuantity n a b c)) * nashQuantity n a b c
        - b * (nashQuantity n a b c) ^ 2 := by
    unfold ownProfit
    rw [hS]
    ring
  have e2 : ownProfit n a b c (nashProfile n a b c hb hca) i xi.val
      = (a - c - b * (((n : ℝ) - 1) * nashQuantity n a b c)) * xi.val
        - b * xi.val ^ 2 := by
    unfold ownProfit
    rw [hS]
    ring
  rw [e1, e2]
  exact hquad

/-- Theorem 1 (uniqueness): every symmetric Nash profile equals the candidate.
(Tirole 1988, Ch. 7.1: uniqueness via strict concavity of profits.) -/
theorem cournotNash_unique_symmetric (n : ℕ) (a b c : ℝ) (hn : 0 < n)
    (hb : 0 < b) (hca : c < a) (q : Fin n → { q : ℝ // 0 ≤ q })
    (hsymm : ∀ i j : Fin n, (q i).val = (q j).val)
    (hNash : (cournotGame n a b c hn).IsNash q) (i : Fin n) :
    (q i).val = nashQuantity n a b c := by
  rw [Econlib.GameTheory.StrategicGame.isNash_iff] at hNash
  have hS : ∑ j ∈ Finset.univ.erase i, (q j).val
      = ((n : ℝ) - 1) * (q i).val := by
    have h1 : ∑ j ∈ Finset.univ.erase i, (q j).val
        = ∑ j ∈ Finset.univ.erase i, (q i).val :=
      Finset.sum_congr rfl (fun j _ => hsymm j i)
    rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h2 : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
      rw [Nat.cast_add, Nat.cast_one] at h2
      linarith
    rw [hcast]
  -- (q i).val is the unique maximizer, hence the best-response formula.
  have h1 : ∀ y : ℝ, 0 ≤ y →
      (a - c - b * (((n : ℝ) - 1) * (q i).val)) * y - b * y ^ 2
        ≤ (a - c - b * (((n : ℝ) - 1) * (q i).val)) * (q i).val
          - b * ((q i).val) ^ 2 := by
    intro y hy
    have hN := hNash i ⟨y, hy⟩
    rw [payoff_eq_ownProfit, payoff_update_eq] at hN
    dsimp only at hN
    have e1 : ownProfit n a b c q i y
        = (a - c - b * (((n : ℝ) - 1) * (q i).val)) * y - b * y ^ 2 := by
      unfold ownProfit
      rw [hS]
      ring
    have e2 : ownProfit n a b c q i (q i).val
        = (a - c - b * (((n : ℝ) - 1) * (q i).val)) * (q i).val
          - b * ((q i).val) ^ 2 := by
      unfold ownProfit
      rw [hS]
      ring
    rw [e1, e2] at hN
    exact hN
  have hval : (q i).val
      = max 0 ((a - c - b * (((n : ℝ) - 1) * (q i).val)) / (2 * b)) :=
    quad_max_unique b hb _ _ (q i).property (h1 _ (le_max_left 0 _))
  -- Solve v = max 0 ((a − c − b(n−1)v)/(2b)): the zero branch contradicts a > c.
  by_cases hle : (a - c - b * (((n : ℝ) - 1) * (q i).val)) / (2 * b) ≤ 0
  · rw [max_eq_left hle] at hval
    have hcon : (0 : ℝ)
        < (a - c - b * (((n : ℝ) - 1) * (q i).val)) / (2 * b) := by
      have h2b : (0 : ℝ) < 2 * b := by linarith
      rw [hval]
      simp only [mul_zero, sub_zero]
      exact div_pos (by linarith) h2b
    linarith
  · rw [not_le] at hle
    rw [max_eq_right (le_of_lt hle)] at hval
    have h2b : (2 : ℝ) * b ≠ 0 := ne_of_gt (by linarith)
    have h2 : (q i).val * (2 * b)
        = a - c - b * (((n : ℝ) - 1) * (q i).val) := by
      have hdm := div_mul_cancel₀
        (a - c - b * (((n : ℝ) - 1) * (q i).val) : ℝ) h2b
      rw [← hval] at hdm
      exact hdm
    have hring : b * (q i).val * ((n : ℝ) + 1)
        = 2 * b * (q i).val + b * (((n : ℝ) - 1) * (q i).val) := by ring
    have h3 : (q i).val * (b * ((n : ℝ) + 1)) = a - c := by
      linear_combination h2 + hring
    have hbN : b * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by
      have h1b : (0 : ℝ) < b := hb
      have h2n : (0 : ℝ) < (n : ℝ) + 1 := by
        have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact mul_pos h1b h2n)
    unfold nashQuantity
    rw [eq_div_iff hbN]
    exact h3

end Leancollusion
