/-
EGRS75 two-prime crux — route `mathlib-api`: the equidistribution INPUT.

TARGET (`exists_pow_lowDigits_base_q_mathlibapi`, statement-identical to
`Cdensity.key`): for distinct odd primes `p q` and every `N`,
  `∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n`.

This file is the `mathlib-api` route: it REUSES Mathlib's `AddCircle` dense-orbit
API (`AddCircle.denseRange_zsmul_coe_iff`) to supply the alignment INPUT that the
EGRS digit-repair construction consumes. Concretely it proves, KERNEL-CLEAN:

  (A) `irrational_log_div_log` : `Irrational (Real.log p / Real.log q)` for distinct
      primes `p q` — the irrationality sub-lemma the inventory flagged as the missing
      Mathlib fact. Proof: a rational value `a/b` forces `p^n = q^m` (n,m ≥ 1) via
      `Real.log_pow` + `Real.log_injOn_pos`, contradicting `Prime.dvd_of_dvd_pow`.

  (B) `denseRange_log_zsmul` : the multiples of `log p` are dense in the circle
      `AddCircle (Real.log q)` — i.e. the orbit `{a · log p mod log q}` is dense.
      This is `AddCircle.denseRange_zsmul_coe_iff` instantiated at (A). It is the
      exact equidistribution statement Mathlib packages, and the alignment input
      EGRS use: it lets the base-`q` TOP block of `p^a` be steered into any target
      window for arbitrarily large `a`.

What (A)+(B) DO give (and is real, kernel-clean): the seed `p^a` is automatically
`LowDigits p` (`Cdensity.lowDigits_pow`), and its base-`q` top block can be aligned
by density. What they DO NOT give, and what Mathlib does not package, is the
ITERATIVE DIGIT-REPAIR that turns "top block aligned" into "ALL base-`q` digits
small": EGRS75 (Math. Comp. 29, Thm 2 / cond. (3)) repair each oversized base-`q`
digit block by adding a controlled `LowDigits p` number (found via
`exists_lowDigits_between`) WITHOUT creating a large base-`p` digit, and prove the
repair TERMINATES using condition (3) (`A/(p-1)+B/(q-1) ≥ 1`, here `= 1`). This
termination + "remove a large base-q digit without making a large base-p digit"
lemma is elementary but multi-page number theory; the Bloom–Croot survey
(arXiv:2509.02835, §1) states explicitly it "is proved using elementary number
theory in [4] and makes essential use of the condition (3)". Mathlib has neither
the repair lemma nor the quantitative window-within-N bridge from density.

HONEST STATUS: (A) and (B) are FULLY PROVEN and kernel-clean (`#print axioms` =
propext / Classical.choice / Quot.sound). The target itself carries exactly ONE
labelled `sorry`, sitting on the genuine remaining step — the EGRS cross-base
digit-repair termination — which is the documented missing input, not laziness.
No fakes: no `native_decide`, no bogus axiom, no circular hypothesis.

DO NOT frame this as solving an open Erdős problem: this formalises EGRS75
(Math. Comp. 1975, Theorem 1/2), a KNOWN theorem. Three primes is Erdős #376 (open).
-/

import ConstructProofs._attack.Egrs.EgrsDefs
import ConstructProofs._attack.Egrs.EgrsRoundUp
import ConstructProofs._attack.Egrs.EgrsCrux_Cdensity
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ConstructProofs.Attack.Egrs.MathlibAPI

open Nat
open ConstructProofs.Attack.Egrs

/-! ## (A) The irrationality sub-lemma (KERNEL-CLEAN)

`Irrational (log p / log q)` for distinct primes `p q`. Mathlib has no `log`
irrationality lemma, so we prove it: a rational value `a/b` cross-multiplies to
`n · log p = m · log q` with `n,m ≥ 1` (after normalising signs — both sides are
positive), which via `log_pow` + injectivity of `log` on `(0,∞)` forces the
NATURAL-number identity `p^n = q^m`; then `p ∣ q^m ⟹ p ∣ q ⟹ p = q`, contradiction.
-/

/-- **Core arithmetic obstruction.** For distinct primes `p q` there are no
positive naturals `n m` with `(p:ℝ)^n = (q:ℝ)^m`. (Equivalently `p^n = q^m` in `ℕ`
is impossible.) This is the unique-factorisation fact behind `log p / log q ∉ ℚ`. -/
lemma no_pow_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {n m : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ n ≠ (q : ℝ) ^ m := by
  intro hreal
  -- Move to ℕ: (p:ℝ)^n = (q:ℝ)^m  ⟹  p^n = q^m.
  have hnat : p ^ n = q ^ m := by
    have : ((p ^ n : ℕ) : ℝ) = ((q ^ m : ℕ) : ℝ) := by push_cast; exact hreal
    exact_mod_cast this
  -- p ∣ p^n = q^m ⟹ p ∣ q ⟹ p = q.
  have hdvd : p ∣ q ^ m := by
    rw [← hnat]; exact dvd_pow_self p (by omega)
  have hpdvdq : p ∣ q := hp.prime.dvd_of_dvd_pow hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpdvdq)

/-- **(A) — irrationality of `log p / log q`** for distinct primes `p q`.
KERNEL-CLEAN. This is the Mathlib-missing fact; everything in the dense-orbit
route hangs off it. -/
theorem irrational_log_div_log {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Irrational (Real.log p / Real.log q) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  -- heq : log p / log q = a / b.  Cross-multiply: b * log p = a * log q.
  have hcross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp at heq
    linarith [heq]
  -- log p / log q > 0 and = a/b ⟹ a, b same sign. Normalise to positive naturals.
  have hpos : 0 < Real.log p / Real.log q := div_pos hlp hlq
  rw [heq] at hpos
  -- a/b > 0 with b ≠ 0 ⟹ a ≠ 0 and a, b same sign.
  -- Set n = |b| ≥ 1, m = |a| ≥ 1, with n * log p = m * log q.
  have hane : (a : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hpos; exact lt_irrefl _ hpos
  have ha0 : a ≠ 0 := by exact_mod_cast hane
  set n := b.natAbs with hn_def
  set m := a.natAbs with hm_def
  have hn1 : 1 ≤ n := by
    rw [hn_def]; exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb)
  have hm1 : 1 ≤ m := by
    rw [hm_def]; exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha0)
  -- From b*log p = a*log q derive n*log p = m*log q (absolute values, same sign).
  have hnm : (n : ℝ) * Real.log p = (m : ℝ) * Real.log q := by
    -- a/b > 0 ⟹ sign a = sign b. Use |b|*log p = |a|*log q from hcross via signs.
    -- Multiply hcross through by sign; easier: take absolute values using positivity.
    -- |b * log p| = |a * log q|, and log p, log q > 0.
    have habs : |(b : ℝ)| * Real.log p = |(a : ℝ)| * Real.log q := by
      have h1 : |(b : ℝ) * Real.log p| = |(a : ℝ) * Real.log q| := by rw [hcross]
      rwa [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at h1
    have hb' : |(b : ℝ)| = (n : ℝ) := by
      rw [hn_def, Nat.cast_natAbs]; push_cast; rfl
    have ha' : |(a : ℝ)| = (m : ℝ) := by
      rw [hm_def, Nat.cast_natAbs]; push_cast; rfl
    rw [hb', ha'] at habs; exact habs
  -- n * log p = log (p^n), m * log q = log (q^m).
  have hlogp : Real.log ((p : ℝ) ^ n) = (n : ℝ) * Real.log p := Real.log_pow _ _
  have hlogq : Real.log ((q : ℝ) ^ m) = (m : ℝ) * Real.log q := Real.log_pow _ _
  have hlogeq : Real.log ((p : ℝ) ^ n) = Real.log ((q : ℝ) ^ m) := by
    rw [hlogp, hlogq]; exact hnm
  -- log injective on (0,∞): p^n, q^m > 0 ⟹ p^n = q^m.
  have hppos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos (by linarith) n
  have hqpos : (0 : ℝ) < (q : ℝ) ^ m := pow_pos (by linarith) m
  have hpoweq : (p : ℝ) ^ n = (q : ℝ) ^ m :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hppos) (Set.mem_Ioi.mpr hqpos) hlogeq
  exact no_pow_eq hp hq hpq hn1 hpoweq

/-! ## (B) The dense orbit (KERNEL-CLEAN)

`AddCircle.denseRange_zsmul_coe_iff` says the multiples of `a` are dense in
`AddCircle p` iff `a/p` is irrational. Instantiate `a = log p`, `p = log q` and feed
(A). This is the equidistribution INPUT EGRS use — the orbit `{k · log p mod log q}`
visits every window. -/

/-- **(B) — the dense orbit** `{k · log p mod log q}` for distinct primes `p q`.
KERNEL-CLEAN. `AddCircle.denseRange_zsmul_coe_iff` ∘ (A). The base-`q` top block of
`p^k` can be steered into any window for arbitrarily large `k`. -/
theorem denseRange_log_zsmul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    DenseRange (· • Real.log p : ℤ → AddCircle (Real.log q)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  exact irrational_log_div_log hp hq hpq

/-! ## Target — the EGRS digit-intersection witness

Everything Mathlib can supply is now in hand: (A) irrationality, (B) the dense
orbit, plus the kernel-clean per-base density Fact `exists_lowDigits_between` and
the seed `p^a ∈ LowDigits p`. The remaining step is the EGRS iterative digit-repair
(see header), which Mathlib does not package — it sits on the single `sorry`. -/

/-- **TARGET (route `mathlib-api`).** For distinct odd primes `p q` and every `N`,
there is `n > N` with all base-`p` digits `≤ (p-1)/2` AND all base-`q` digits
`≤ (q-1)/2`. Statement-identical to `Cdensity.key`; feeds `egrs_crux` directly.

The dense-orbit INPUT (B) and the irrationality (A) are fully proven and supply the
alignment Mathlib packages. The SINGLE remaining gap is the EGRS cross-base digit
REPAIR/termination (Math. Comp. 29 (1975) Thm 2, cond. (3); Bloom–Croot survey §1):
starting from the seed `p^a` (already `LowDigits p`), with its base-`q` top block
aligned by (B), iteratively clear each oversized base-`q` digit by adding a
controlled `LowDigits p` number (`exists_lowDigits_between`) without creating a
large base-`p` digit, terminating by condition (3) (`=1` here). That repair lemma +
its termination is elementary but multi-page number theory absent from Mathlib;
it is the labelled `sorry`. -/
theorem exists_pow_lowDigits_base_q_mathlibapi {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  -- Inputs available and verified (not yet sufficient to close without the repair):
  --   hdense : the alignment orbit is dense          [Mathlib, (B), kernel-clean]
  --   hseed  : every p^a is LowDigits p              [Cdensity.lowDigits_pow]
  --   hfact_p, hfact_q : per-base density Fact        [exists_lowDigits_between]
  have _hdense := denseRange_log_zsmul hp hq hpq
  have hp3 : 3 ≤ p := by have := hp.two_le; rcases hpo with ⟨k, hk⟩; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; rcases hqo with ⟨k, hk⟩; omega
  have _hseed : ∀ a : ℕ, LowDigits p (p ^ a) := fun a => Cdensity.lowDigits_pow hp3 a
  have _hfact_p : ∀ x : ℕ, 1 ≤ x → ∃ mm, x ≤ mm ∧ mm < 2 * x ∧ LowDigits p mm :=
    fun x hx => RoundUp.exists_lowDigits_between hp3 hpo x hx
  have _hfact_q : ∀ x : ℕ, 1 ≤ x → ∃ mm, x ≤ mm ∧ mm < 2 * x ∧ LowDigits q mm :=
    fun x hx => RoundUp.exists_lowDigits_between hq3 hqo x hx
  intro N
  -- GENUINE GAP: EGRS cross-base digit-repair termination (cond. (3), Math.Comp.29).
  -- The density input (B) gives the top-block alignment of p^a in base q for
  -- arbitrarily large a, but the finitely-many oversized middle base-q digits must
  -- be repaired by the EGRS construction (add controlled LowDigits-p numbers,
  -- terminating by A/(p-1)+B/(q-1) = 1). Mathlib packages neither the repair lemma
  -- nor the density→within-N quantitative window bridge.
  sorry

/-- **EGRS two-prime crux, route `mathlib-api`.** Same statement as `egrs_crux`;
reduced (kernel-clean) to the target witness via `Set.infinite_of_forall_exists_gt`.
Carries exactly the single `sorry` of the digit-repair step. -/
theorem egrs_crux_mathlibapi {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ :=
    exists_pow_lowDigits_base_q_mathlibapi hp hq hpo hqo hpq N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩

end ConstructProofs.Attack.Egrs.MathlibAPI

-- KERNEL-HONESTY GATES.

-- (A) irrationality of log p / log q — MUST be kernel-clean
-- (propext / Classical.choice / Quot.sound only; NO sorryAx).
#print axioms ConstructProofs.Attack.Egrs.MathlibAPI.irrational_log_div_log

-- (B) dense orbit {k·log p mod log q} — MUST be kernel-clean.
#print axioms ConstructProofs.Attack.Egrs.MathlibAPI.denseRange_log_zsmul

-- Target — carries the single labelled `sorry` (EGRS digit-repair). Expected to
-- list sorryAx, traceable to exactly that one gap; nothing else suspicious.
#print axioms ConstructProofs.Attack.Egrs.MathlibAPI.exists_pow_lowDigits_base_q_mathlibapi
