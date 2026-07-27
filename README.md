# EGRS75 two-prime theorem — a machine-checked proof in Lean 4

## MISHA mission

My son Misha has a rare genetic hearing loss. I am building an independent AI
research lab for rare diseases. Every result that survives formal checking and
outside review is one step toward that lab—and toward tools that may help
millions of people.

One rare disease is rare. Rare diseases together are not.

This theorem has no claimed biomedical application. Its role is to test the
research pipeline: can AI-assisted work recover a hard proof from the
literature, formalize it, expose dependency mistakes, and survive kernel and
outside review? A lab we can trust in biology first needs a workflow we can
trust in mathematics.

[Erdős–Graham–Ruzsa–Straus (Math. Comp. **29** (1975) 83–92), Theorem 1, two-prime case]:
for any two distinct odd primes `p, q` there are infinitely many `n` with

```
p ∤ C(2n, n)   and   q ∤ C(2n, n).
```

This repository contains a complete, kernel-checked Lean 4 / Mathlib proof — including
the iterated carry-controlled digit-clearing step that Bloom–Croot
([arXiv:2509.02835](https://arxiv.org/abs/2509.02835), §1) defer verbatim to the 1975
paper. Companion paper: *A Machine-Checked Proof of the Erdős–Graham–Ruzsa–Straus
Two-Prime Theorem* (draft, 2026).

## Main results

| Theorem | File |
|---|---|
| `ConstructProofs.Attack.Egrs.MuFinish.egrs_two_prime_mu` | `ConstructProofs/_attack/Egrs/EgrsMuFinish_20260612.lean` |
| `ConstructProofs.Attack.Egrs.Finish.egrs_two_prime_finish` (bad-bit-mask assembly; low case from `MuFinish`) | `ConstructProofs/_attack/Egrs/EgrsFinish_core.lean` |

Both print exactly

```
[propext, Classical.choice, Quot.sound]
```

under `#print axioms` — **no `sorryAx`, no `native_decide`, no extra axioms.**
Selected load-bearing lemmas and both headline theorems have explicit
`#print axioms` gates. CI requires the headline gates and re-runs them on every
build.

The two final theorems are not independent proofs: `Finish` imports `MuFinish`
and uses `MuFinish.egrs_clearing_low_mu` to discharge its low case. They do use
different outer assemblies, but share the decisive μ-based clearing result.

## Verifying the claim

1. **Build** (toolchain `leanprover/lean4:v4.29.1`, Mathlib pinned by
   `lake-manifest.json`):

   ```sh
   lake exe cache get
   lake build
   ```

   The build log prints the axiom gates; the headline gates are at the bottom of
   `EgrsMuFinish_20260612.lean` and `EgrsFinish_core.lean`.

2. **Comparator** (adversarial third-party check; Linux): the
   [`comparator/egrs75/`](comparator/egrs75/) workspace states the theorem in
   Mathlib-only vocabulary (`Challenge.lean`) and bridges it to this development
   (`Solution.lean`). Running [leanprover/comparator](https://github.com/leanprover/comparator)
   verifies statement identity, the axiom budget, and kernel acceptance in a
   sandboxed export-level pipeline. See `comparator/egrs75/README.md`.

3. **Self-report**: [`formalization.yaml`](formalization.yaml) (the
   [mathlib-initiative standard](https://github.com/mathlib-initiative/formalization.yaml))
   documents sources, scope, automation methods, fidelity divergences, and the
   statement-alignment table.

## Honesty notes

- This is **known** mathematics (1975); no open problem is solved here. The
  `r ≥ 3` analogues (Erdős #376/#406, Graham's $1,000 question on
  `C(2n,n) ⊥ 105`) are open and untouched.
- Only the equality case `A = (p−1)/2, B = (q−1)/2` (the central-binomial
  corollary) is formalized — not the general `(A, B)` digit-bound Theorem 1.
- A few **scaffold declarations outside the main results' dependency cone**
  carry a `sorry` (e.g. `egrs_crux` in `EgrsDefs.lean` and the parked targets in
  `EgrsCrux_Cdensity.lean` / `Equidist_mathlibapi.lean` — earlier reduction
  routes kept for the historical record; the file headers say so). The kernel
  gates prove the main results do **not** depend on any of them: a single
  `sorryAx` anywhere in the cone would appear in the `#print axioms` output.
- This development was produced with substantial AI assistance (Anthropic
  Claude, agentic sessions) and audited by the Lean kernel; see
  `formalization.yaml` → `automation` for methods and costs.

## Layout

```
ConstructProofs/
├── Erdos376Bridge.lean            Kummer carry transducer (digit characterization)
├── ConcreteMath/KummerBridge.lean p-adic valuation bridge
└── _attack/Egrs/                  the EGRS75 development
    ├── EgrsDefs.lean              LowDigits, the Kummer bridge, the reduction
    ├── EgrsRoundUp.lean           half-density fact (every [x,2x) meets D_p)
    ├── EgrsLeaf_induction.lean    bad-digit count, seed lemmas
    ├── EgrsRepair_digitvector.lean / EgrsRepair_paperfaithful.lean
    │                              bad-index set, digit-at-index toolkit
    ├── EgrsClearing_P2/P3/P4      carry windows, controlled subtraction, condition (3)
    ├── EgrsCrux_Cdensity.lean / Equidist_mathlibapi.lean
    │                              earlier routes (kept; irrationality lemma reused)
    ├── EgrsSeedWindow_20260612.lean   Dirichlet seed (condition (2))
    ├── EgrsMoveDigits_20260612.lean   staircase lemma + carry arithmetic
    ├── EgrsMuFinish_20260612.lean     μ-measure, the single move, the theorem
    ├── EgrsFinish_core.lean           second route (bad-bit-mask induction)
    └── EgrsSmokeProbe_20260612.lean   no-vacuity probes + comparator challenge form
comparator/egrs75/                 leanprover/comparator workspace
formalization.yaml                 self-report (mathlib-initiative standard)
```

## License

Apache 2.0 (see `LICENSE`).
