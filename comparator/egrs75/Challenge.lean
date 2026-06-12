/-
TRUSTED CHALLENGE — the EGRS75 two-prime theorem, Mathlib vocabulary only.

This file is the comparator (leanprover/comparator) challenge: the exact
statement whose proof is claimed by the accompanying development.  It imports
only Mathlib; no project definitions appear in the statement.

Erdős–Graham–Ruzsa–Straus, "On the prime factors of (2n choose n)",
Math. Comp. 29 (1975) 83–92, Theorem 1 (two-prime case).
-/

import Mathlib

/-- For any two distinct odd primes `p q` there are infinitely many `n` with
`p ∤ C(2n,n)` and `q ∤ C(2n,n)`. -/
theorem egrs_two_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by
  sorry
