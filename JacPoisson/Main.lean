/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import JacPoisson.Defs

/-!
# The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`

Adjamagbo and van den Essen (arXiv:math/0608009, Theorem 7(1), from Theorem 1). Let `φ` be an
endomorphism of the `n`-th canonical Poisson algebra and `F v = φ (X v)`.

* The bracket of two components of `F` is an entry of `Jᵀ Ω J`, where `J` is the Jacobian of `F`
  and `Ω` the matrix of the canonical bracket on the generators (`poissonBracket_eq_mul`). So
  `φ` preserves the bracket on the generators exactly when `Jᵀ Ω J = Ω`. Since `Ω` is minus
  Mathlib's `Matrix.J`, the Jacobian is then in Mathlib's symplectic group, and its determinant
  is a unit (`isUnit_det_jacobian`). The paper shows that the determinant is `1` when `n!` is
  invertible; a unit is all that the Jacobian conjecture asks for.
* The Jacobian conjecture, moved from the variables `Fin (2 * n)` to `Fin n ⊕ Fin n`
  (`jacobianConjectureProp_congr`), gives a polynomial map `G` inverse to `F`, and `bind₁ G` is
  inverse to `φ = bind₁ F` (`bijective_of_inverse`).
-/

@[expose] public section

namespace JacPoisson

open MvPolynomial Matrix JacobianConjecture

section Bracket

variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]

/-- The bracket of two components of a polynomial map is an entry of `Jᵀ (-J₀) J`, where `J` is
the map's Jacobian and `J₀ = Matrix.J` the canonical skew-symmetric matrix. -/
theorem poissonBracket_eq_mul (F : RegularFunction R (l ⊕ l) (l ⊕ l)) (v w : l ⊕ l) :
    poissonBracket (F v) (F w) =
      (F.Jacobianᵀ * (-Matrix.J l (MvPolynomial (l ⊕ l) R)) * F.Jacobian) v w := by
  simp only [poissonBracket, RegularFunction.Jacobian, Matrix.J, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, neg_zero, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  simp only [neg_neg, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_mul,
    Finset.sum_sub_distrib]
  ring

omit [Fintype l] in
/-- The Jacobian of the identity map is the identity matrix. -/
theorem jacobian_id : (RegularFunction.id R (l ⊕ l)).Jacobian = 1 := by
  ext a b
  simp only [RegularFunction.Jacobian, RegularFunction.id, Matrix.of_apply, pderiv_X,
    Matrix.one_apply, Pi.single_apply, eq_comm]

/-- A polynomial map preserving the canonical bracket on the generators has a unit Jacobian
determinant. -/
theorem isUnit_det_jacobian (F : RegularFunction R (l ⊕ l) (l ⊕ l))
    (hF : ∀ v w, poissonBracket (F v) (F w) = poissonBracket (X v) (X w)) :
    IsUnit F.Jacobian.det := by
  have hΩ : F.Jacobianᵀ * (-Matrix.J l (MvPolynomial (l ⊕ l) R)) * F.Jacobian =
      -Matrix.J l (MvPolynomial (l ⊕ l) R) := by
    refine Matrix.ext fun v w => ?_
    have h := hF v w
    rw [poissonBracket_eq_mul, show (X v : MvPolynomial (l ⊕ l) R) =
      RegularFunction.id R (l ⊕ l) v from rfl, show (X w : MvPolynomial (l ⊕ l) R) =
      RegularFunction.id R (l ⊕ l) w from rfl, poissonBracket_eq_mul, jacobian_id] at h
    simpa using h
  have hmem : F.Jacobian ∈ symplecticGroup l (MvPolynomial (l ⊕ l) R) := by
    rw [SymplecticGroup.mem_iff']
    simpa [Matrix.mul_neg, Matrix.neg_mul] using hΩ
  exact SymplecticGroup.symplectic_det hmem

end Bracket

section Congr

variable {k : Type*} [CommRing k] {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]

/-- The Jacobian conjecture for one set of variables gives it for any equivalent set. -/
theorem jacobianConjectureProp_congr (e : σ ≃ τ) (h : JacobianConjectureProp k σ) :
    JacobianConjectureProp k τ := by
  intro F hF
  -- `F` in the variables `σ`.
  set F' : RegularFunction k σ σ := fun s => rename e.symm (F (e s)) with hF'
  have hJ : F'.Jacobian =
      (reindex e.symm e.symm F.Jacobian).map (rename e.symm : MvPolynomial τ k →ₐ[k] _) := by
    ext a b
    have := pderiv_rename (R := k) e.symm.injective (e a) (F (e b))
    simp only [Equiv.symm_apply_apply] at this
    simp [RegularFunction.Jacobian, hF', this]
  have hF'det : IsUnit F'.Jacobian.det := by
    rw [hJ, ← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_reindex_self]
    exact hF.map _
  obtain ⟨G', hGF, hFG⟩ := h F' hF'det
  refine ⟨fun t => rename e (G' (e.symm t)), ?_, ?_⟩
  · funext t
    have := congrFun hGF (e.symm t)
    simp only [RegularFunction.comp, RegularFunction.id, hF', bind₁_rename,
      Equiv.apply_symm_apply] at this
    simp only [RegularFunction.comp, RegularFunction.id]
    have h2 := congrArg (rename e) this
    rw [rename_bind₁, rename_X, Equiv.apply_symm_apply] at h2
    simpa [Function.comp_def] using h2
  · funext t
    have := congrFun hFG (e.symm t)
    simp only [RegularFunction.comp, RegularFunction.id, hF'] at this
    simp only [RegularFunction.comp, RegularFunction.id, bind₁_rename]
    have h2 := congrArg (rename e) this
    rw [rename_X, Equiv.apply_symm_apply, rename_bind₁] at h2
    simp only [rename_rename, Equiv.self_comp_symm, rename_id_apply] at h2
    simpa [Function.comp_def] using h2

end Congr

section Inverse

variable {k : Type*} [CommRing k] {σ : Type*}

/-- An algebra endomorphism whose images of the generators have a two-sided polynomial inverse
is bijective. -/
theorem bijective_of_inverse (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (G : RegularFunction k σ σ)
    (hGF : G.comp (fun v => φ (X v)) = RegularFunction.id k σ)
    (hFG : RegularFunction.comp (fun v => φ (X v)) G = RegularFunction.id k σ) :
    Function.Bijective φ := by
  generalize hF : (fun v => φ (X v)) = F at hGF hFG
  have hφ : φ = bind₁ F := by
    ext v
    simp [← hF]
  rw [hφ]
  refine Function.bijective_iff_has_inverse.mpr ⟨bind₁ G, fun p => ?_, fun p => ?_⟩
  · have h : (fun i => bind₁ G (F i)) = X := hGF
    rw [bind₁_bind₁, h, bind₁_X_left, AlgHom.id_apply]
  · have h : (fun i => bind₁ F (G i)) = X := hFG
    rw [bind₁_bind₁, h, bind₁_X_left, AlgHom.id_apply]

end Inverse

open Arxiv.«math.0608009»

/-- **The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`**
(Adjamagbo and van den Essen, Theorem 7(1)). -/
theorem jacobian_implication {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n := by
  intro φ hφ
  have hJ := jacobianConjectureProp_congr ((finCongr (two_mul n)).trans finSumFinEquiv.symm) h
  obtain ⟨G, hGF, hFG⟩ := hJ (fun v => φ (X v)) (isUnit_det_jacobian _ hφ)
  exact bijective_of_inverse φ G hGF hFG

end JacPoisson
