/-
Numeric anchors: `#eval` cross-checks against the verified simulation outputs.

These do not prove anything; they guard against vacuous formalization by
pinning the closed forms to the numbers the oligopoly repository's benchmarks
check to 1e-6 (see oligopoly/README.md, "Correctness").
-/
import Leancollusion.RepeatedCollusion

namespace Leancollusion

/-- Asymmetric Cournot-Nash formula (not proved here; included as a numeric
anchor). For n firms with costs c_i and demand P = a − bQ:
q_i* = (a − (n+1)·c_i + Σc_j) / (b·(n+1)).
(oligopoly/src/sim/strategies/nash_strategies.py: `cournot_nash_equilibrium`.) -/
def asymNashFloat (a b : Float) (costs : List Float) (i : Nat) : Float :=
  let n := costs.length.toFloat
  let csum := costs.foldl (· + ·) 0
  (a - (n + 1) * costs[i]! + csum) / (b * (n + 1))

-- oligopoly README: fictitious-play quantities converge to ≈ Nash (30.7, 28.7)
-- for a=100, b=1, costs=[10,12].
#eval asymNashFloat 100 1 [10, 12] 0  -- expected: 30.666666666666668
#eval asymNashFloat 100 1 [10, 12] 1  -- expected: 28.666666666666668

-- Exact rational anchors: 92/3 = 30.666…, 86/3 = 28.666….
#eval (92 / 3 : ℚ)
#eval (86 / 3 : ℚ)

-- Symmetric special case pinned to Theorem 1's closed form:
-- n=2, a=100, b=1, c=10 gives (100−10)/(1·3) = 30.
#eval ((100 - 10 : Float) / (1 * (2 + 1)))  -- expected: 30.0

/-- Critical discount factor as Float (mirror of `criticalDiscount`). -/
def criticalDiscountFloat (n : Float) : Float := (n + 1)^2 / (n^2 + 6*n + 1)

-- v2: δ* for duopoly is the textbook 9/17 ≈ 0.5294 (Tirole 1988, Ch. 6.3.2).
#eval criticalDiscountFloat 2  -- expected: 0.5294117647058824
#eval criticalDiscountFloat 3  -- expected: 0.5714285714285714

-- v2 payoff anchors at a=100, b=1, c=10, n=2 (mirrors of the closed forms):
-- π^C = (a−c)²/(4bn) = 1012.5, π^N = (a−c)²/(b(n+1)²) = 900.0,
-- π^D = (a−c)²(n+1)²/(16bn²) = 1139.0625.
#eval ((100 - 10 : Float)^2 / (4 * 1 * 2))                -- expected: 1012.5
#eval ((100 - 10 : Float)^2 / (1 * (2 + 1)^2))            -- expected: 900.0
#eval ((100 - 10 : Float)^2 * (2 + 1)^2 / (16 * 1 * 2^2))  -- expected: 1139.0625

end Leancollusion
