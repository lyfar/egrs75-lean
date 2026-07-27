# Comparator workspace — EGRS75 two-prime theorem

Third-party mechanical verification of the headline claim of this repository's
EGRS75 development, via [leanprover/comparator](https://github.com/leanprover/comparator):

> **Claim.** `Solution.lean` proves *exactly* the statement in `Challenge.lean`
> (Erdős–Graham–Ruzsa–Straus 1975, two-prime theorem), is accepted by the Lean
> kernel, and uses no axioms beyond `propext`, `Quot.sound`, `Classical.choice`.

## Layout

- `Challenge.lean` — the TRUSTED statement, Mathlib vocabulary only (`import Mathlib`;
  no project definitions in the statement), with `sorry`.
- `Solution.lean` — byte-identical statement, proved by the development's
  `egrs_two_prime_mu` (`ConstructProofs/_attack/Egrs/EgrsMuFinish_20260612.lean`).
- `config.json` — comparator configuration (theorem `egrs_two_prime`, the three
  standard axioms permitted, nanoda off by default).
- `lakefile.toml` — workspace package requiring `construct_proofs` by path (`../..`),
  which transitively pins Mathlib `v4.29.1`.

## Running comparator

Comparator's sandbox (`landrun`, Linux Landlock) requires **Linux**; this workspace
is prepared on macOS and must be *run* on a Linux host or CI.  Follow the pinned-tool
setup of [leanprover/lean-eval](https://github.com/leanprover/lean-eval) (see its
`SECURITY.md` pin table), with one adjustment: build `lean4export` and `comparator`
with a toolchain compatible with **this** workspace's `lean-toolchain`
(`leanprover/lean4:v4.29.1`) — a toolchain mismatch shows up as
`failed to read file '.../Challenge.olean', incompatible header`, which is an
install problem, not a proof problem.

```sh
# inside this directory, on Linux, with landrun/lean4export/comparator on PATH
lake exe cache get          # Mathlib cache for the transitive dependency
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory $(pwd) -- \
  bash -c 'lake env comparator config.json'
```

## What is already verified locally (macOS, this repository)

- The development builds with **zero errors** (full package, 8,329 jobs).
- `#print axioms` on `egrs_two_prime_mu` (and the second outer assembly
  `egrs_two_prime_finish`, which reuses the μ-based low-case result) prints exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`.
- The challenge statement is provable by the development **verbatim**:
  `SmokeProbe.egrs_two_prime_challenge_form`
  (`ConstructProofs/_attack/Egrs/EgrsSmokeProbe_20260612.lean`) restates
  `Challenge.lean`'s theorem byte-for-byte and closes it by
  `egrs_two_prime_mu`; it compiles kernel-clean.

The comparator run adds: an *adversarial-setting* re-check of statement identity,
axiom budget, and kernel acceptance in a sandboxed, export-level pipeline that does
not trust this repository's build outputs.
