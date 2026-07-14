# Certifying this repository with `comparator`

[`leanprover/comparator`](https://github.com/leanprover/comparator) is a trustworthy judge
for Lean proofs. Here it is used as a **self-audit**: it checks that the development really
proves the statements this repository claims, using only the axioms this repository admits.

Given `Challenge.lean` (the statements, importing *Mathlib only*, proofs `sorry`) and
`Solution.lean` (a bare re-export of the development), comparator independently verifies:

1. **Statement match** — every constant in the transitive closure of the certified
   statements is *identical* in both environments. A `complexity` or `kernelViolators`
   that drifted from the one in `Challenge.lean` is caught here.
2. **Axiom discipline** — the proofs reach for no axiom outside the config's
   `permitted_axioms`, and a permitted axiom's *type* is compared across both
   environments too (so a cited axiom cannot be quietly restated as `False`).
3. **Kernel replay** — the exported solution environment is re-accepted from scratch by
   the Lean kernel, via `lean4export` + `Lean4Checker`, without loading any `.olean`.

Auditing the headline claims therefore reduces to **reading `Challenge.lean`**.

## The two configs

The repository's docstrings claim an axiom stratification; these configs pin it down
mechanically, and CI fails if it ever regresses.

| Config | Theorem | Permitted axioms |
| --- | --- | --- |
| `kernel.json` | `TH.superlinear_of_kernel` — the Stage-1 reduction (K) ⟹ M4 | `propext`, `Quot.sound`, `Classical.choice` |
| `capstone.json` | `TH.superlinear_of_middleBand` — the conditional capstone | the above **+** `Subspace.evertseSchlickewei` |
| `superlinear.json` | `TH.kernel_holds`, `TH.complexity_superlinear` — **the headline: M4** | the above **+** `Subspace.evertseSchlickewei` |

So `superlinear.json` certifies the program's target — the steering word of the `(3/2)^n`
orbit has superlinear subword complexity — resting on the Subspace Theorem and *nothing
else*: no `sorry`, no second axiom, no open hypothesis. `kernel.json` separately certifies
that the Stage-1 reduction leans on no cited literature at all, and `capstone.json` keeps
the axiom-input-free conditional form of record honest.

The stratification is enforced, not decorative: swapping `capstone.json` or
`superlinear.json` to the standard axioms alone makes comparator report
`Illegal axiom detected: 'Subspace.evertseSchlickewei'`.

## Install

Comparator is a Lake dependency (`lakefile.lean`), so Lake builds it and `lean4export` at
the toolchain this project pins — nothing to install by hand:

```sh
lake build comparator lean4export
```

`landrun` is the one exception: it has no pinned release, so build it from source. It uses
**Landlock**, so this is **Linux-only** (check with `grep LANDLOCK /boot/config-$(uname -r)`);
building it needs [Go](https://go.dev/dl/).

```sh
git clone https://github.com/Zouuup/landrun && cd landrun
go build -o ~/.local/bin/landrun cmd/landrun/main.go   # ensure ~/.local/bin is on PATH
```

## Run

```sh
lake build Challenge Solution   # prebuild: the sandbox has no network
lake test                       # runs comparator on both configs
```

A successful run prints `Your solution is okay!` once per config. To run a single config:

```sh
lake test -- comparator/kernel.json
```

Each binary can be overridden by environment variable — `COMPARATOR_BIN`,
`COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN` — which is also how to substitute
comparator's `scripts/fake-landrun.sh` shim on a machine without Landlock. That shim does
**not** sandbox anything; it still exercises the statement match, the axiom check and the
kernel replay, which are the three properties that matter for a self-audit.

## A note on the sandbox

Comparator's threat model targets an *adversarial* solution: it sandboxes every build with
`landrun` and, for full hardening against a known landrun escape (fixed in Linux 7.1), asks
to be wrapped in

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- bash -c 'lake test'
```

Here the solution is our own code, so the sandbox is belt-and-braces; the load-bearing
guarantees are the statement match, the axiom check, and the independent kernel replay.
That is also why CI prebuilds `Challenge` and `Solution` outside the sandbox (which has no
network, and `Challenge` imports all of Mathlib).

CI: `.github/workflows/comparator.yml`.
