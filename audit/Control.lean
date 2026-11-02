/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import JacPoisson

/-!
# Controls

* The axiom audit would catch a `sorry`: `#print axioms` reports `sorryAx` for an unproved
  statement.
* The result specialises to the rationals in the one open case, `n = 1`.
* On the generators, the bracket matrix is minus Mathlib's `Matrix.J`: `{X₁, X₂} = 1`, the sign
  `poissonBracket_eq_mul` assumes.
* The determinant lemma applies to a Poisson endomorphism that is not linear, the shear
  `x ↦ x`, `y ↦ y + x²`.
-/

open MvPolynomial Arxiv.«math.0608009» JacobianConjecture JacPoisson

public theorem unproved : PoissonConjectureFor ℚ 1 := by
  sorry

/-- info: 'unproved' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unproved

example (h : JacobianConjectureProp ℚ (Fin 2)) : PoissonConjectureFor ℚ 1 :=
  Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication 1 h

example :
    poissonBracket (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℚ) (X (Sum.inr 0)) = 1 ∧
    -Matrix.J (Fin 1) (MvPolynomial (Fin 1 ⊕ Fin 1) ℚ) (Sum.inl 0) (Sum.inr 0) = 1 := by
  constructor
  · simp [poissonBracket, pderiv_X]
  · simp [Matrix.J]

/-- The shear `x ↦ x`, `y ↦ y + x²` preserves the bracket, so its Jacobian determinant is a
unit. -/
example : IsUnit (RegularFunction.Jacobian (k := ℚ)
    (Sum.elim (fun _ => X (Sum.inl 0)) (fun _ => X (Sum.inr 0) + X (Sum.inl 0) ^ 2) :
      RegularFunction ℚ (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1))).det := by
  refine isUnit_det_jacobian _ fun v w => ?_
  rcases v with v | v <;> rcases w with w | w <;> fin_cases v <;> fin_cases w <;>
    simp [poissonBracket, pderiv_X, Pi.single_apply]
