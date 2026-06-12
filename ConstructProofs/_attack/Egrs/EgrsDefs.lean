/-
EGRS75 two-prime infinitude — strategy + defs scaffold.

Erdős–Graham–Ruzsa–Straus 1975, "On the prime factors of binomial coefficients"
(Math. Comput. 29 (1975) 83–92).

TARGET (`egrs_two_prime`): for distinct odd primes `p q`,
  `{n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite`.

This file performs the BRIDGE REDUCTION only. It assembles the single-base
Kummer→digit characterisation we already hold KERNEL-CLEAN in
  ConstructProofs/Erdos376Bridge.lean      (`coprime_centralBinom_prime_iff`)
  ConstructProofs/ConcreteMath/KummerBridge.lean
into the predicate `LowDigits p n` ("every base-`p` digit of `n` is `≤ (p-1)/2`"),
proves `¬ p ∣ Nat.centralBinom n ↔ LowDigits p n` (kernel-clean), and reduces the
target to the CRUX `egrs_crux`:
  `{n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite`.

The crux is the genuine theorem (counting-exponent density argument:
θ_p + θ_q > 1 for all distinct odd p,q) and is left as the single labelled
`sorry`. Three primes is Erdős #376 (OPEN) — do NOT attempt here.

Recon / context: MATH CONTEXT block in the run prompt; #376 recon at
  ~/Knowledge/Construct/recon/erdos_376.md
DO NOT reprove Kummer — reuse the imports below.
-/

import ConstructProofs.Erdos376Bridge
import Mathlib.Data.Set.Finite.Basic

namespace ConstructProofs.Attack.Egrs

open Nat

/-! ## The digit predicate -/

/-- `LowDigits p n`: every base-`p` digit of `n` is `≤ (p-1)/2`.
This is the Kummer no-carry condition for doubling `n` in base `p`
(`p ∤ C(2n,n)`). For an **odd** prime `p`, `d ≤ (p-1)/2 ↔ 2*d < p`, so it is
the same predicate as #376's `LowDoubleDigits p n := ∀ d ∈ digits p n, 2*d < p`
(see `lowDigits_iff_lowDoubleDigits` below). -/
def LowDigits (p n : ℕ) : Prop := ∀ d ∈ Nat.digits p n, d ≤ (p - 1) / 2

/-- For an **odd** prime `p`, the per-digit bound `2*d < p` (the #376 form, i.e.
"doubling produces no carry") is equivalent to `d ≤ (p-1)/2` (the `LowDigits`
form). The hypotheses are stated per-digit so the lemma threads through the
`∀ d ∈ digits p n` quantifier. -/
lemma digit_le_half_iff_two_mul_lt {p d : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    d ≤ (p - 1) / 2 ↔ 2 * d < p := by
  obtain ⟨k, hk⟩ := hpodd
  -- p = 2k+1, so (p-1)/2 = k and the claim is `d ≤ k ↔ 2*d < 2k+1 ↔ 2*d ≤ 2k`.
  subst hk
  have hhalf : (2 * k + 1 - 1) / 2 = k := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]; exact Nat.mul_div_cancel_left k (by decide)
  rw [hhalf]; omega

/-- `LowDigits` and #376's `LowDoubleDigits` coincide for odd primes. -/
theorem lowDigits_iff_lowDoubleDigits {p n : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    LowDigits p n ↔ Construct.Erdos376.LowDoubleDigits p n := by
  unfold LowDigits Construct.Erdos376.LowDoubleDigits
  constructor
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mp (h d hd)
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mpr (h d hd)

/-! ## The single-base bridge (KERNEL-CLEAN — assembled from #376)

`coprime_centralBinom_prime_iff` (Erdos376Bridge) gives, for any prime `p`:
  `Coprime (centralBinom n) p ↔ LowDoubleDigits p n`.
We turn `Coprime _ p` into `¬ p ∣ _` and `LowDoubleDigits` into `LowDigits`
(odd prime), yielding the single-base fact we already hold. -/

/-- **EGRS single-base bridge.** For an **odd prime** `p`,
`p ∤ C(2n,n)` exactly when every base-`p` digit of `n` is `≤ (p-1)/2`.
Kernel-clean: assembled from `coprime_centralBinom_prime_iff` + odd-prime digit
arithmetic. This is the per-prime Kummer fact the two-prime target stands on. -/
theorem not_dvd_centralBinom_iff_lowDigits {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (n : ℕ) : ¬ p ∣ Nat.centralBinom n ↔ LowDigits p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcop := Construct.Erdos376.coprime_centralBinom_prime_iff (p := p) n
  -- `Coprime (centralBinom n) p ↔ ¬ p ∣ centralBinom n`
  have hnotdvd : Nat.Coprime (Nat.centralBinom n) p ↔ ¬ p ∣ Nat.centralBinom n := by
    rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  rw [← hnotdvd, hcop, ← lowDigits_iff_lowDoubleDigits hp2 hpodd]

/-! ## The crux (density argument) — single labelled `sorry`

A_p := {n | LowDigits p n} has counting exponent θ_p = log((p+1)/2)/log p.
For distinct odd primes, θ_p + θ_q > 1 (smallest pair 3,5 already gives
≈ 0.631 + 0.683 = 1.314), which forces A_p ∩ A_q infinite. This is the genuine
EGRS75 two-prime theorem and the ONLY remaining gap. -/

/-- **EGRS two-prime crux.** For distinct odd primes `p q`, the set of `n`
whose base-`p` AND base-`q` digits are all `≤ (p-1)/2`, `(q-1)/2` respectively
is infinite. THIS IS THE GAP route agents must close (counting-exponent /
density argument; θ_p + θ_q > 1 for all distinct odd p,q). -/
theorem egrs_crux {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  sorry

/-! ## Target, reduced to the crux -/

/-- **EGRS75 two-prime target.** For distinct odd primes `p q`, there are
infinitely many `n` with `p ∤ C(2n,n)` and `q ∤ C(2n,n)`. Reduced — via the
kernel-clean single-base bridge — to `egrs_crux`. (Currently depends on the
`egrs_crux` `sorry`; the reduction itself is real and bridge-clean.) -/
theorem egrs_two_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by
  -- Rewrite the digit-free set as the LowDigits set via the single-base bridge,
  -- then invoke the crux.
  have hset :
      {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n} =
        {n : ℕ | LowDigits p n ∧ LowDigits q n} := by
    ext n
    simp only [Set.mem_setOf_eq]
    rw [not_dvd_centralBinom_iff_lowDigits hp hpo n,
        not_dvd_centralBinom_iff_lowDigits hq hqo n]
  rw [hset]
  exact egrs_crux hp hq hpo hqo hpq

end ConstructProofs.Attack.Egrs

-- Kernel-honesty gate for the bridge reduction lemma (must be clean:
-- propext / Classical.choice / Quot.sound only; NO sorryAx).
#print axioms ConstructProofs.Attack.Egrs.not_dvd_centralBinom_iff_lowDigits
