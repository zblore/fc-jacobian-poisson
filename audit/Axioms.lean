/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import JacPoisson

/-!
# Axioms of the main results

Fails if any main result comes to depend on anything beyond Lean's three standard axioms.
-/

/--
info: 'Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication

/--
info: 'PoissonConjecture.poisson_conjecture.variants.jacobian_implication' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonConjecture.poisson_conjecture.variants.jacobian_implication

/--
info: 'JacPoisson.isUnit_det_jacobian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms JacPoisson.isUnit_det_jacobian

/--
info: 'JacPoisson.jacobianConjectureProp_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms JacPoisson.jacobianConjectureProp_congr
