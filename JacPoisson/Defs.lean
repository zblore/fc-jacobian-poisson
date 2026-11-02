/-
Copyright 2025-2026 The Formal Conjectures Authors.
Modifications copyright 2026 Zayn Blore.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Formal Conjectures' definitions

Copied verbatim from Formal Conjectures (`google-deepmind/formal-conjectures`, commit
`a64e959c32c270df4dd0d96d2027481f15750534`), with Formal Conjectures' names:

* `MvPolynomial.RegularFunction` and its API, the whole of
  `FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean`;
* `MvPolynomial.poissonBracket`, from
  `FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean`;
* `JacobianConjecture.JacobianConjectureProp`, from
  `FormalConjectures/Wikipedia/JacobianConjecture.lean`;
* `Arxiv.«math.0608009».IsPoissonEndomorphism` and `Arxiv.«math.0608009».PoissonConjectureFor`,
  from `FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean`.

Each file's imports are replaced by `Mathlib`. `scripts/check-fc-match.py` checks the text.
-/

@[expose] public section

namespace MvPolynomial

variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}

variable (k σ τ) in
/-- The type of regular functions from $k^σ$ to $k^τ$. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- The Jacobian of a vector valued polynomial function, viewed as a polynomial. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)

/-- The composition of two vector valued polynomial functions. -/
noncomputable def comp
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)

variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

/-- The evaluation of a regular function `f` over `k` at some point `a`
with coordinates in some algebra over `k`-/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

/--`aeval` is compatible with composition of regular functions. -/
lemma comp_aeval
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction

end MvPolynomial

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [Fintype σ]

/-- The canonical Poisson bracket on `MvPolynomial (σ ⊕ σ) R`, given by
$\{f, g\} = \sum_{i} (\partial_{x_i} f \cdot \partial_{y_i} g
- \partial_{y_i} f \cdot \partial_{x_i} g)$ where $x_i$ (resp. $y_i$) is the variable
indexed by `Sum.inl i` (resp. `Sum.inr i`). -/
noncomputable def poissonBracket (f g : MvPolynomial (σ ⊕ σ) R) : MvPolynomial (σ ⊕ σ) R :=
  ∑ i : σ, (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g -
    pderiv (Sum.inr i) f * pderiv (Sum.inl i) g)

end MvPolynomial

namespace JacobianConjecture

open MvPolynomial RegularFunction

/-- The predicate that the Jacobian conjecture holds for a given field and variable index type
(i.e. number of variables). -/
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

end JacobianConjecture

namespace Arxiv.«math.0608009»

open MvPolynomial JacobianConjecture

variable {K : Type*} [Field K] [CharZero K]

/-- A `K`-algebra endomorphism `φ` of the polynomial algebra in $2n$ variables is an
endomorphism of the `n`-th canonical Poisson algebra $P_n(K)$ if it preserves the canonical
Poisson bracket. Following [AvdE07], Lemma 2, it is equivalent to require preservation on
the generators only, which is the form used here (the brackets of generators are constants,
so preserving and intertwining them agree). -/
def IsPoissonEndomorphism {n : ℕ}
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K) : Prop :=
  ∀ v w, poissonBracket (φ (X v)) (φ (X w)) = poissonBracket (X v) (X w)

variable (K) in
/-- The Poisson Conjecture in dimension `n` ($PC_n$ in the notation of [AvdE07]): every
endomorphism of the `n`-th canonical Poisson algebra over `K` is an automorphism.
An endomorphism is an automorphism iff it is bijective, since the inverse of a bijective
algebra endomorphism preserving the Poisson bracket is again such. -/
def PoissonConjectureFor (n : ℕ) : Prop :=
  ∀ φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K,
    IsPoissonEndomorphism φ → Function.Bijective φ

end Arxiv.«math.0608009»
