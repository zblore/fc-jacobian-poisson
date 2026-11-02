# The Jacobian conjecture implies the Poisson conjecture: a Lean proof

A Lean 4 proof that the Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n, over any field of characteristic zero. It proves the statement `poisson_conjecture.variants.jacobian_implication` from the file `Arxiv/math.0608009/PoissonConjecture.lean` in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), against their own definitions and under their own name.

## The result

Take polynomials in 2n variables x₁, …, xₙ, y₁, …, yₙ over a field of characteristic zero, with the canonical Poisson bracket, so that {xᵢ, yⱼ} = 1 when i = j and 0 otherwise, {yᵢ, xⱼ} = −{xⱼ, yᵢ}, and {xᵢ, xⱼ} = {yᵢ, yⱼ} = 0. A Poisson endomorphism is a substitution that preserves this bracket. The Poisson conjecture in dimension n says that every Poisson endomorphism is invertible. The Jacobian conjecture in dimension m says that every polynomial map of m-space whose Jacobian determinant is a unit has a polynomial inverse.

K. Adjamagbo and A. van den Essen, "A proof of the equivalence of the Dixmier, Jacobian and Poisson conjectures", Acta Math. Vietnam. 32 (2007), 205–214 (arXiv:math/0608009), Theorem 7, proved a chain of implications: the Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n, which implies the Dixmier conjecture in dimension n, which implies the Jacobian conjecture in dimension n. This repository proves the first link.

The Jacobian conjecture is now known to be false from dimension 3 on, and the Poisson conjecture from dimension 2 on. The implication is still not empty: the Jacobian conjecture in dimension 2 is open, and so is the Poisson conjecture in dimension 1, so the case n = 1 cannot be settled by either counterexample.

## The proof

The paper derives the implication from its Theorem 1: an endomorphism preserves the bracket exactly when its Jacobian matrix is symplectic, and then its Jacobian determinant is 1. Formal Conjectures' Jacobian conjecture only asks that the determinant be a unit, which allows a shorter route than the paper's volume forms.

- **The bracket as a matrix product.** Write F for the images of the 2n variables and J for its Jacobian matrix. The bracket of two components of F is an entry of Jᵀ Ω J, where Ω is the matrix of brackets of the variables (`poissonBracket_eq_mul`). So F preserves the bracket on the variables exactly when Jᵀ Ω J = Ω.
- **A unit determinant.** Ω is minus Mathlib's `Matrix.J`, so J lies in Mathlib's symplectic group, and Mathlib's `symplectic_det` says its determinant is a unit (`isUnit_det_jacobian`). This holds over any commutative ring.
- **Changing variables.** Formal Conjectures indexes the variables by `Fin n ⊕ Fin n` for the Poisson conjecture and by `Fin (2 * n)` for the Jacobian conjecture. The Jacobian conjecture for one set of variables gives it for any equivalent set, by renaming (`jacobianConjectureProp_congr`).
- **The inverse.** The Jacobian conjecture then gives a polynomial map G inverse to F. The endomorphism is substitution by F, so substitution by G is its inverse, and it is bijective (`bijective_of_inverse`).

The files:

- `Challenge.lean`: the statement, for Palomar. It imports only Mathlib, so the definitions it uses are copied into it from Formal Conjectures, word for word. Palomar does not accept names like `Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication`, with its escaped `«math.0608009»`, so the theorem is stated in the namespace `PoissonConjecture`, with the same leaf name. The definitions keep Formal Conjectures' names, so the statement is the same. `Solution` proves it under both names.
- `Solution.lean`: imports the proof.
- `JacPoisson/Defs.lean`: the same definitions, copied from Formal Conjectures.
- `JacPoisson/Main.lean`: the proof.
- `JacPoisson/FormalTarget.lean`: the Formal Conjectures statement.

`lake comparator` checks that `Solution` proves exactly the statement of `Challenge.lean`, with the same definitions; with this repository's `comparator.json` it replays the proof through Lean's kernel and nanoda. CI runs it through `scripts/verify-comparator.sh`, copied unchanged from Palomar's template, which adds con-ron, the toolchain's second bundled independent kernel. Palomar's own pipeline, which `.github/workflows/palomar-preflight.yml` runs on a chosen commit, runs con-ron separately, in a version its maintainers pin, and is the check that decides acceptance. `JacPoisson/FormalTarget.lean` proves the statement under Formal Conjectures' name too, and checks in Lean that both names have the same statement at every universe level.

`scripts/check-fc-match.py` checks the other link: that `Challenge.lean` is Formal Conjectures' definitions and statement, character for character, and nothing else. It also checks that nothing earlier in Formal Conjectures' four source files (a `variable`, `open`, notation, option, instance or declaration, including one behind a modifier such as `public`) could change what the copied text means. With `--self-test` it checks that 32 altered files fail: altered copies of `Challenge.lean` (a changed universe, an extra hypothesis, a shadowing definition, a weakened Jacobian condition, and others), of `JacPoisson/FormalTarget.lean`, and of Formal Conjectures' files.

`audit/Axioms.lean` checks that the proofs use only `propext`, `Classical.choice` and `Quot.sound`, and it fails if that ever changes. `audit/Control.lean` checks that the audit would catch a `sorry` (an unproved statement reports `sorryAx`), specialises the result to the rationals for n = 1, checks the bracket sign against Mathlib's `Matrix.J`, and applies the determinant lemma to a Poisson endomorphism that is not linear.

## Building

It needs Lean v4.35.0-rc3 and Mathlib at commit `5e0c4e52`.

```
lake exe cache get
lake build
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-lean-sources.py
python3 scripts/check-fc-match.py --self-test
```

The library builds in under a minute once Mathlib is in place. `scripts/verify-comparator.sh` runs `lake comparator` as Palomar's template does; it needs Linux, for its sandbox.

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics. My proof that the Poisson conjecture is false from dimension 2 on is Palomar entry [PALOMAR-2026-11-01-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000002).
