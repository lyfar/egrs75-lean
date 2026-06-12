/-
EGRS75 two-prime crux — route C (density / counting lower bound).

Goal (same statement as `ConstructProofs.Attack.Egrs.egrs_crux`):
for distinct odd primes `p q`,
  `{n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite`.

`LowDigits p n := ∀ d ∈ Nat.digits p n, d ≤ (p-1)/2`  (from `EgrsDefs`).

ROUTE C — the counting exponent of `A_p := {n | LowDigits p n}` is
`θ_p = log((p+1)/2)/log p`; at `N = p^a` the count is *exactly* `((p+1)/2)^a`.
For distinct odd primes `θ_p + θ_q > 1` (smallest pair 3,5 gives ≈ 1.314), which is
the density condition behind the intersection being infinite.

STATUS (honest): this file proves the REAL, kernel-clean infrastructure of route C
and isolates the single genuine gap at one labelled `sorry`. Concretely it proves:

  * `lowDigits_iff_getD`         — digit predicate via `n / p^i % p`  (clean)
  * `lowDigits_zero`             — `0 ∈ A_p`                          (clean)
  * `lowDigits_pow`              — every `p^k ∈ A_p`                  (clean)
  * `Set.Infinite` of each single `A_p` via the powers              (clean)
  * `count_lowDigits_pow`        — EXACT count `#{n<p^a : LowDigits p n} = ((p+1)/2)^a`
                                   — the θ_p exponent made exact      (clean)
  * `exists_lowDigits_between`   — EGRS's density "Fact": every `[x,2x)` contains a
                                   `LowDigits p` number (proven kernel-clean in
                                   `EgrsRoundUp.lean` via the round-up map `ru`)  (clean)
  * the reduction `egrs_crux_Cdensity` to one `key` lemma            (clean)

The single `sorry` sits on `key`: the CROSS-BASE Diophantine alignment (EGRS eq. (2)
+ iterative digit-repair). The per-base density Fact is now PROVEN; what remains is
exactly the incommensurable-bases alignment that makes the two digit conditions
hold simultaneously. See the long comment at `key` for the precise remaining gap.
This was confirmed against the primary source (Erdős–Graham–Ruzsa–Straus 1975,
Math. Comp. 29, pp. 83–92, proof of Theorem 1): the gap is genuine, not laziness —
it needs Diophantine input Mathlib does not package, and is not a clean one-session
elementary argument.
-/

import ConstructProofs._attack.Egrs.EgrsDefs
import ConstructProofs._attack.Egrs.EgrsRoundUp
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Order.Preorder.Finite

namespace ConstructProofs.Attack.Egrs.Cdensity

open Nat
open ConstructProofs.Attack.Egrs

-- `count_lowDigits_pow`'s statement filters by the (classically decidable)
-- predicate `LowDigits p`; we use classical decidability rather than threading a
-- `DecidablePred` instance. This is pure-logic `Classical.choice`, already in the
-- kernel-clean axiom set; it is NOT used to discharge any proof obligation.
set_option linter.style.openClassical false
open scoped Classical

/-! ## Digit predicate, restated pointwise

`Nat.getD_digits : 2 ≤ b → (digits b n).getD i 0 = n / b ^ i % b`, so the `i`-th
base-`b` digit of `n` is `n / b^i % b`. We turn `LowDigits` (a `∀ d ∈ digits …`)
into the pointwise `∀ i, n / p^i % p ≤ (p-1)/2`, which is the form the counting
argument manipulates. -/

/-- Every entry of `digits b n` equals `n / b^i % b` for the matching index `i`,
and conversely every such quotient that is nonzero-relevant appears. We only need
the forward "membership ⇒ it is some `n / b^i % b`" plus the pointwise bound. -/
lemma mem_digits_eq_getD {b n d : ℕ} (hb : 2 ≤ b) (hd : d ∈ Nat.digits b n) :
    ∃ i, i < (Nat.digits b n).length ∧ d = n / b ^ i % b := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hd
  refine ⟨i, hi, ?_⟩
  have hgd := Nat.getD_digits n i hb
  rw [List.getD_eq_getElem (Nat.digits b n) 0 hi, hget] at hgd
  exact hgd

/-- Pointwise reformulation: `LowDigits p n` iff every `n / p^i % p ≤ (p-1)/2`.
The reverse direction uses that any digit is of this form (`mem_digits_eq_getD`);
the forward direction needs that `n / p^i % p`, when it is a *genuine* digit
(i.e. `i` within length), lies in `digits p n`. We package only what `key`'s
helpers consume: forward (digit ⇒ bound) is exactly `LowDigits`. -/
lemma lowDigits_iff_getD {p n : ℕ} (hp : 2 ≤ p) :
    LowDigits p n ↔ ∀ i, i < (Nat.digits p n).length → n / p ^ i % p ≤ (p - 1) / 2 := by
  unfold LowDigits
  constructor
  · intro h i hi
    have hmem : (Nat.digits p n)[i] ∈ Nat.digits p n := List.getElem_mem hi
    have hval := Nat.getD_digits n i hp
    rw [List.getD_eq_getElem (Nat.digits p n) 0 hi] at hval
    rw [← hval]
    exact h _ hmem
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := mem_digits_eq_getD hp hd
    exact h i hi

/-! ## Basic membership facts (kernel-clean) -/

/-- `0` has no digits, hence `LowDigits p 0` holds vacuously. -/
lemma lowDigits_zero (p : ℕ) : LowDigits p 0 := by
  unfold LowDigits
  rw [Nat.digits_zero]
  intro d hd
  exact absurd hd (List.not_mem_nil)

/-- For an odd prime base, the digit `1` is `≤ (p-1)/2`. Used to show powers of `p`
are low-digit (their only nonzero digit is `1`). -/
lemma one_le_half {p : ℕ} (hp : 3 ≤ p) : (1 : ℕ) ≤ (p - 1) / 2 := by
  have : 2 ≤ p - 1 := by omega
  calc (1 : ℕ) = 2 / 2 := by norm_num
    _ ≤ (p - 1) / 2 := Nat.div_le_div_right this

/-- Every power `p^k` is low-digit in base `p` (for `p ≥ 3`): its base-`p` digit
list is `[0,…,0,1]`, all entries `≤ (p-1)/2`. -/
lemma lowDigits_pow {p : ℕ} (hp : 3 ≤ p) (k : ℕ) : LowDigits p (p ^ k) := by
  have hp1 : 1 < p := by omega
  unfold LowDigits
  intro d hd
  -- digits p (p^k) = replicate k 0 ++ [1]
  have hk : Nat.digits p (p ^ k) = List.replicate k 0 ++ Nat.digits p 1 := by
    have := Nat.digits_base_pow_mul (b := p) (k := k) (m := 1) hp1 (by norm_num)
    simpa using this
  rw [hk] at hd
  rw [List.mem_append] at hd
  rcases hd with hd | hd
  · rw [List.mem_replicate] at hd
    omega
  · rw [Nat.digits_of_lt p 1 (by norm_num) (by omega)] at hd
    simp only [List.mem_singleton] at hd
    rw [hd]
    exact one_le_half hp

/-! ## Each single `A_p` is infinite (kernel-clean)

The powers `p^k` are strictly increasing and all in `A_p`, so `A_p` is unbounded,
hence infinite. (This is the trivial `θ_p > 0` content; the genuine theorem is the
*intersection* of two such sets.) -/

/-- `N < p ^ (N+1)` for `p ≥ 2`, via `N < 2^N ≤ 2^(N+1) ≤ p^(N+1)`. -/
lemma lt_pow_succ {p : ℕ} (hp : 2 ≤ p) (N : ℕ) : N < p ^ (N + 1) := by
  have h2 : (2 : ℕ) ^ (N + 1) ≤ p ^ (N + 1) := Nat.pow_le_pow_left hp _
  have hN : N < 2 ^ (N + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

lemma single_infinite {p : ℕ} (hp : 3 ≤ p) :
    {n : ℕ | LowDigits p n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  exact ⟨p ^ (N + 1), lowDigits_pow hp _, lt_pow_succ (by omega) N⟩

/-! ## Exact counting at base powers (kernel-clean): the θ_p exponent

`count_lowDigits_pow`: `#{n < p^a : LowDigits p n} = ((p+1)/2)^a`.

This is the exact form of the density exponent `θ_p = log((p+1)/2)/log p`:
the number of low-digit residues with `a` base-`p` digits is exactly the number of
digit strings of length `a` with each digit in `{0,…,(p-1)/2}`, i.e. `((p-1)/2 + 1)^a
= ((p+1)/2)^a`. We prove it by induction on `a` via the digit recursion
`n = n % p + p * (n / p)` (`Nat.digits_add_two_add_one`-style split): a number
`n < p^(a+1)` is low-digit iff its last digit `n % p ≤ (p-1)/2` and `n / p < p^a` is
low-digit. -/

/-- Splitting lemma: for `p ≥ 2`, `LowDigits p n` holds iff the last digit
`n % p ≤ (p-1)/2` and `LowDigits p (n / p)`. -/
lemma lowDigits_split {p n : ℕ} (hp : 2 ≤ p) (hn : n ≠ 0) :
    LowDigits p n ↔ n % p ≤ (p - 1) / 2 ∧ LowDigits p (n / p) := by
  unfold LowDigits
  have hp1 : 1 < p := by omega
  rw [Nat.digits_def' hp1 (Nat.pos_of_ne_zero hn)]
  constructor
  · intro h
    refine ⟨h _ (List.mem_cons_self ..), fun d hd => h _ (List.mem_cons_of_mem _ hd)⟩
  · rintro ⟨h0, hrec⟩ d hd
    rw [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact h0
    · exact hrec _ hd

/-- Unconditional split (covers `n = 0` too). -/
lemma lowDigits_split' {p n : ℕ} (hp : 2 ≤ p) :
    LowDigits p n ↔ n % p ≤ (p - 1) / 2 ∧ LowDigits p (n / p) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.zero_mod, Nat.zero_div]
    refine ⟨fun _ => ⟨Nat.zero_le _, lowDigits_zero p⟩, fun _ => lowDigits_zero p⟩
  · exact lowDigits_split hp hn

/-- The exact count of low-digit numbers below `p^a` is `((p+1)/2)^a`.
Equivalently `((p-1)/2 + 1)^a`; we keep the `+1` form to match the digit recursion.
KERNEL-CLEAN target. -/
lemma count_lowDigits_pow {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    ((Finset.range (p ^ a)).filter (fun n => LowDigits p n)).card
      = ((p - 1) / 2 + 1) ^ a := by
  induction a with
  | zero =>
    rw [pow_zero, pow_zero, Finset.range_one]
    rw [Finset.filter_true_of_mem]
    · simp
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact lowDigits_zero p
  | succ a ih =>
    -- Bijection  {n < p^(a+1) : LowDigits p n}  ≃
    --   range((p-1)/2+1) ×ˢ {m < p^a : LowDigits p m}
    -- via  n ↦ (n % p, n / p),  (d,m) ↦ d + p*m.
    have hp0 : 0 < p := by omega
    have hpa : 0 < p ^ a := pow_pos hp0 a
    have hhlt : (p - 1) / 2 < p := by omega
    have hcard :
        ((Finset.range (p ^ (a + 1))).filter (fun n => LowDigits p n)).card
          = ((Finset.range ((p - 1) / 2 + 1)) ×ˢ
              ((Finset.range (p ^ a)).filter (fun m => LowDigits p m))).card := by
      apply Finset.card_nbij' (fun n => (n % p, n / p)) (fun dm => dm.1 + p * dm.2)
      · -- MapsTo i
        intro n hn
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨hnlt, hnlow⟩ := hn
        rw [lowDigits_split' hp] at hnlow
        obtain ⟨hmod, hdiv⟩ := hnlow
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter,
          Finset.mem_range]
        dsimp only
        refine ⟨by omega, ?_, hdiv⟩
        rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
        exact hnlt
      · -- MapsTo j
        intro dm hdm
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter,
          Finset.mem_range] at hdm
        obtain ⟨hd, hmlt, hmlow⟩ := hdm
        have hdp : dm.1 < p := by omega
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · -- d + p*m < p^(a+1) = p * p^a
          calc dm.1 + p * dm.2 < p + p * dm.2 := by omega
            _ = p * (dm.2 + 1) := by ring
            _ ≤ p * p ^ a := Nat.mul_le_mul_left p (by omega)
            _ = p ^ (a + 1) := by rw [pow_succ, Nat.mul_comm]
        · rw [lowDigits_split' hp]
          refine ⟨?_, ?_⟩
          · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdp]; omega
          · rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hdp]; simpa using hmlow
      · -- LeftInvOn
        intro n _
        simp only
        rw [Nat.mod_add_div]
      · -- RightInvOn
        intro dm hdm
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_filter,
          Finset.mem_range] at hdm
        obtain ⟨hd, _, _⟩ := hdm
        have hdp : dm.1 < p := by omega
        have h1 : (dm.1 + p * dm.2) % p = dm.1 := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdp]
        have h2 : (dm.1 + p * dm.2) / p = dm.2 := by
          rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hdp, Nat.zero_add]
        dsimp only
        rw [h1, h2]
    rw [hcard, Finset.card_product, Finset.card_range, ih, pow_succ]
    ring

/-! ## The single-base density "Fact" is now PROVEN (kernel-clean import)

`EgrsRoundUp.exists_lowDigits_between` (proven kernel-clean in `EgrsRoundUp.lean`
via the explicit round-up map `ru`) is the load-bearing density input of EGRS75's
proof of their Theorem 1:

  for odd `p ≥ 3` and every `x ≥ 1`, the interval `[x, 2x)` contains a
  `LowDigits p` number.

We re-export it under a route-C name. This is REAL: it is exactly the EGRS "Fact"
that consecutive `LowDigits p` numbers differ by a factor `< 2` (`A = (p-1)/2`,
ratio `(p-1)/A = 2`). It is the per-base half of the argument, done. -/

/-- **EGRS density Fact** (per base, kernel-clean — proven in `EgrsRoundUp`).
For an odd prime `p` and every `x ≥ 1`, some `m ∈ [x, 2x)` is `LowDigits p`. -/
theorem exists_lowDigits_between {p : ℕ} (hp : p.Prime) (hpo : Odd p) {x : ℕ}
    (hx : 1 ≤ x) : ∃ m, x ≤ m ∧ m < 2 * x ∧ LowDigits p m := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hpo with ⟨k, hk⟩; omega
  exact RoundUp.exists_lowDigits_between hp3 hpo x hx

/-! ## The crux, reduced to one genuine gap (the cross-base Diophantine alignment)

`Set.infinite_of_forall_exists_gt` reduces `Infinite` to: for every `N` there is
`n > N` in the set. That is exactly `key` below. Everything else in this file —
the digit predicate, the exact `θ_p` count `count_lowDigits_pow`, single-set
infinitude, AND the per-base density Fact `exists_lowDigits_between` — is real,
kernel-clean infrastructure. The ONLY remaining mathematical gap is `key`. -/

/-- **THE GENUINE GAP (single labelled `sorry`): the cross-base alignment.**

`key`: for distinct odd primes `p q` and every `N`, there is `n > N` whose base-`p`
digits are all `≤ (p-1)/2` AND whose base-`q` digits are all `≤ (q-1)/2`.

This is the entire mathematical content of the EGRS75 two-prime theorem
(Math. Comp. 29 (1975), Theorem 1, with `A = (p-1)/2`, `B = (q-1)/2`, so the
hypothesis `A/(p-1) + B/(q-1) = 1 ≥ 1` holds at equality).

WHAT IS NOW DONE (kernel-clean, in this file / `EgrsRoundUp`):
  * the exact counts `#{n<p^a : LowDigits p n} = ((p+1)/2)^a`  (`count_lowDigits_pow`);
  * the **per-base density Fact**: every `[x,2x)` contains a `LowDigits p` number
    (`exists_lowDigits_between`) — EGRS's "Fact", proven via the round-up map.

WHY THE PER-BASE FACT DOES NOT CLOSE IT (verified): the two Facts give a
`LowDigits p` number and a `LowDigits q` number in every `[x,2x)`, but not the
SAME number. Naive single-interval inclusion–exclusion is unsound: both `A_p`,
`A_q` have density `→ 0` (counts `≍ N^{θ_p}, N^{θ_q}` with `θ_p,θ_q<1`), so
`#A_p+#A_q ≪ N` and the union bound is vacuous. Concretely the both-low set is
EMPTY in `[p^k, 2p^k)` for some `k` (e.g. `p=3,q=5`: empty at `k=1,4`), so no
fixed dyadic-power interval works — the interval must be CHOSEN by the Diophantine
condition.

THE PRECISE REMAINING STEP (EGRS eq. (2) + their repair Lemma): since `log p` and
`log q` are incommensurable, choose arbitrarily large exponents `a` so that the
base-`q` expansion of `p^a` has its top digit already `< B` with the right
spacing (eq. (2)); start from the `(p,A)`-good number `p^a` and iteratively
*repair* each base-`q` digit block that exceeds `B` by adding a `(p,A)`-good number
`U` in a controlled interval (the repair Lemma uses exactly the per-base Fact
`exists_lowDigits_between` to find `U`), terminating in a number that is
simultaneously `(p,A)`-good and `(q,B)`-good. The unproven content is this
Diophantine alignment (eq. 2) together with the termination of the repair — it is
NOT a clean one-session elementary argument and Mathlib lacks the packaged
equidistribution of `{a·log p mod log q}` it needs.

REMAINING GAP, stated exactly: prove
  `∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n`
from `exists_lowDigits_between` (both bases) plus the EGRS Diophantine alignment
of `p^a` in base `q` (eq. (2)) and the iterative digit-repair construction. -/
theorem key {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  sorry

/-- **EGRS two-prime crux, route C.** Same statement as `egrs_crux`. Reduced
(kernel-clean) to `key` via `Set.infinite_of_forall_exists_gt`. -/
theorem egrs_crux_Cdensity {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ := key hp hq hpo hqo hpq N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩

end ConstructProofs.Attack.Egrs.Cdensity

-- KERNEL-CLEAN pieces (must be propext / Classical.choice / Quot.sound only):
#print axioms ConstructProofs.Attack.Egrs.Cdensity.count_lowDigits_pow
#print axioms ConstructProofs.Attack.Egrs.Cdensity.exists_lowDigits_between
#print axioms ConstructProofs.Attack.Egrs.Cdensity.single_infinite
-- Carries the single labelled gap `key` (will report sorryAx — honest):
#print axioms ConstructProofs.Attack.Egrs.Cdensity.egrs_crux_Cdensity
