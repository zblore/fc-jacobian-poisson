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
# The Jacobian conjecture implies the Poisson conjecture

The Poisson conjecture $PC_n$ (K. Adjamagbo and A. van den Essen, arXiv:math/0608009) asserts
that, over a field `K` of characteristic zero, every endomorphism of the `n`-th canonical Poisson
algebra is an automorphism. Their Theorem 7 shows that the Jacobian conjecture in dimension `2n`
implies $PC_n$. The statement below is Formal Conjectures'
`poisson_conjecture.variants.jacobian_implication`.

The definitions below are copied verbatim from Formal Conjectures
(`google-deepmind/formal-conjectures`, commit
`a64e959c32c270df4dd0d96d2027481f15750534`): `MvPolynomial.RegularFunction`,
`RegularFunction.Jacobian`, `RegularFunction.comp` and `RegularFunction.id` from
`FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean`,
`MvPolynomial.poissonBracket` from
`FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean`,
`JacobianConjecture.JacobianConjectureProp` from
`FormalConjectures/Wikipedia/JacobianConjecture.lean`, and the other two from
`FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean`, as is the text of the statement,
with only its `category` and `AMS` attributes left out. Formal Conjectures states it in the
namespace `Arxiv.«math.0608009»`, but Palomar does not accept escaped name components such as
`«math.0608009»` in theorem names, so here it is stated in the namespace `PoissonConjecture`. The
definitions keep their Formal Conjectures names, so the statement is the same term. `Solution`
also proves it under Formal Conjectures' own name.

Formal Conjectures proves that the Jacobian conjecture fails
(`JacobianConjecture.jacobian_conjecture`, in
`FormalConjectures/Wikipedia/JacobianConjecture.lean`). Its map `JacobianConjecture.G` of K³, after
L. Alpöge (2026), has Jacobian determinant 1 and sends (1, 0, 1) and (0, 3, −71) to the same point.
The statement here is proved for every `n`. Its content lies where the Jacobian conjecture in
dimension `2n` is open, in particular `n = 1`.
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

namespace PoissonConjecture

open MvPolynomial JacobianConjecture Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

/--
The Jacobian conjecture in dimension $2n$ implies the Poisson conjecture in dimension `n`
([AvdE07], Theorem 1 and Theorem 7).
-/
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n := by
  sorry

end PoissonConjecture
