/-
SOLUTION BRIDGE — proves the challenge theorem from the development.

The statement below is byte-identical to `Challenge.lean`; the body is a direct
application of the development's `egrs_two_prime_mu`
(`ConstructProofs/_attack/Egrs/EgrsMuFinish_20260612.lean`).
-/

import ConstructProofs._attack.Egrs.EgrsMuFinish_20260612

theorem egrs_two_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  ConstructProofs.Attack.Egrs.MuFinish.egrs_two_prime_mu hp hq hpo hqo hpq
