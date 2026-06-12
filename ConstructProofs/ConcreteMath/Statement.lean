/-
The Concrete Mathematics conjecture on `4`/`9`-divisibility of central
binomial coefficients (Graham–Knuth–Patashnik 1998, exercise 5.112).

Statement: For every `n > 4` with `n ∉ {64, 256}`, the central binomial
coefficient `C(2n, n) = Nat.centralBinom n` is divisible by `4` or by `9`.

Numerical status: Holdum–Klausen–Rasmussen 2026 (arXiv:2601.09510)
verified the statement for every `4 < n ≤ 2^(10^13)` except `n = 64`
and `n = 256`. The conjecture remains open in full generality.

This file gives the formal statement only; no claim of proof is made.
-/

import Mathlib.Data.Nat.Choose.Central

namespace Construct.ConcreteMath

open Nat

/-- The Concrete Mathematics conjecture (Graham–Knuth–Patashnik 1998,
exercise 5.112): for every `n > 4` other than `n = 64` and `n = 256`,
either `4 ∣ C(2n, n)` or `9 ∣ C(2n, n)`. -/
def concreteMath_conjecture : Prop :=
  ∀ n : ℕ, 4 < n → n ≠ 64 → n ≠ 256 →
    (4 ∣ Nat.centralBinom n ∨ 9 ∣ Nat.centralBinom n)

/-- A formal name for the same statement, kept open as a target. No proof
is supplied. -/
def concreteMath_open : Prop := concreteMath_conjecture

/-- The conjecture restricted to `n` being a power of `2`. The reduction
in `Reductions.lean` shows that the full conjecture is equivalent to its
power-of-two restriction (for exponents `k > 2`, `k ≠ 6`, `k ≠ 8`),
because every non-power-of-two `n > 4` has binary popcount `≥ 2`, which
already forces `4 ∣ C(2n, n)`. -/
def concreteMath_powTwo_conjecture : Prop :=
  ∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 → 9 ∣ Nat.centralBinom (2 ^ k)

/-- A formal record that the open conjecture is exactly the stated form. -/
example : concreteMath_open ↔
    (∀ n : ℕ, 4 < n → n ≠ 64 → n ≠ 256 →
       (4 ∣ Nat.centralBinom n ∨ 9 ∣ Nat.centralBinom n)) := Iff.rfl

end Construct.ConcreteMath
