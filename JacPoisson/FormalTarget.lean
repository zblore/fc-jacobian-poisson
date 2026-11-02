/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import JacPoisson.Main

/-!
# The Formal Conjectures statement

`Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication`, with Formal Conjectures'
name, binders and statement (`{K : Type*} [Field K] [CharZero K]`).

Palomar does not accept escaped name components such as `«math.0608009»` in theorem names, so
`Challenge.lean` states the same statement in the namespace `PoissonConjecture`, with Formal
Conjectures' leaf name. It is proved here too, from the one above. The `example` at the end checks
that the two names have the same statement at every universe level, so Comparator's check of the
`PoissonConjecture` name covers Formal Conjectures' name as well.
-/

@[expose] public section

namespace Arxiv.«math.0608009»

open MvPolynomial JacobianConjecture

variable {K : Type*} [Field K] [CharZero K]

/-- **The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`**
(Adjamagbo and van den Essen 2007, Theorem 1 and Theorem 7). -/
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n :=
  JacPoisson.jacobian_implication n h

end Arxiv.«math.0608009»

namespace PoissonConjecture

open MvPolynomial JacobianConjecture Arxiv.«math.0608009»

variable {K : Type*} [Field K] [CharZero K]

/-- **The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`**
(Adjamagbo and van den Essen 2007, Theorem 1 and Theorem 7). -/
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n :=
  Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication n h

end PoissonConjecture

section

universe w

example : type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.variants.jacobian_implication.{w} :=
  rfl

end
