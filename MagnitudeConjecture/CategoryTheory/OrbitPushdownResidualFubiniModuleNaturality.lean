import MagnitudeConjecture.CategoryTheory.OrbitPushdownResidualFubini

/-!
# Module naturality of residual push-down Fubini

The residual Fubini equivalence between iterated and direct Gabriel
push-down is natural not only in orbit objects and morphisms, but also in the
upstairs module.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable {M L : C ⥤ ModuleCat.{uM} k}
variable [M.Additive] [M.Linear k] [L.Additive] [L.Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- The residual Fubini value equivalence commutes with every natural
transformation of upstairs modules. -/
theorem orbitPushdownResidualFubiniLinearEquiv_module_naturality
    (α : M ⟶ L) (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (D.orbitPushdownResidualFubiniLinearEquiv (M := L) N X).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)
          (show ShiftOrbitCategory C (Additive N) from X)) =
      (orbitPushdownNatTransAppLinear (A := Additive G) α X).comp
        (D.orbitPushdownResidualFubiniLinearEquiv
          (M := M) N X).toLinearMap := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  classical
  apply DirectSum.linearMap_ext
  intro q
  apply LinearMap.ext
  intro z
  change DirectSum (Additive N) (fun n ↦
    M.obj ((shiftFunctor C n).obj
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).obj X))) at z
  refine DirectSum.induction_on z ?_ ?_ ?_
  · simp
  · intro n x
    have hx :
        DirectSum.of
            (fun n : Additive N ↦ M.obj ((shiftFunctor C n).obj
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X))) n x =
          orbitPushdownLof M
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X) n x :=
      (orbitPushdownLof_eq_directSumOf M _ n x).symm
    rw [hx]
    simp only [LinearMap.comp_apply]
    rw [DirectSum.lof_eq_of,
      ← orbitPushdownLof_eq_directSumOf
        (orbitPushdown (A := Additive N) M)
          (show ShiftOrbitCategory C (Additive N) from X) q
          (orbitPushdownLof M
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X) n x)]
    change D.orbitPushdownResidualFubiniLinearEquiv (M := L) N X
        (orbitPushdownNatTransAppLinear (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)
          (show ShiftOrbitCategory C (Additive N) from X)
          (orbitPushdownLof (orbitPushdown (A := Additive N) M)
            (show ShiftOrbitCategory C (Additive N) from X) q
            (orbitPushdownLof M
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X) n x))) =
      orbitPushdownNatTransAppLinear (A := Additive G) α X
        (D.orbitPushdownResidualFubiniLinearEquiv (M := M) N X
          (orbitPushdownLof (orbitPushdown (A := Additive N) M)
            (show ShiftOrbitCategory C (Additive N) from X) q
            (orbitPushdownLof M
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X) n x)))
    rw [orbitPushdownNatTransAppLinear_lof]
    change D.orbitPushdownResidualFubiniLinearEquiv (M := L) N X
        (orbitPushdownLof (orbitPushdown (A := Additive N) L)
          (show ShiftOrbitCategory C (Additive N) from X) q
          (orbitPushdownNatTransAppLinear (A := Additive N) α
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X)
            (orbitPushdownLof M
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X) n x))) =
      orbitPushdownNatTransAppLinear (A := Additive G) α X
        (D.orbitPushdownResidualFubiniLinearEquiv (M := M) N X
          (orbitPushdownLof (orbitPushdown (A := Additive N) M)
            (show ShiftOrbitCategory C (Additive N) from X) q
            (orbitPushdownLof M
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X) n x)))
    rw [orbitPushdownNatTransAppLinear_lof]
    simp_rw [orbitPushdownLof_eq_directSumOf]
    unfold orbitPushdownResidualFubiniLinearEquiv
    dsimp only [id]
    change D.residualOrbitPushdownValueLinearEquiv (M := L) N X
        (DirectSum.of
          (fun r : Additive (G ⧸ N) ↦
            DirectSum (Additive N) fun m ↦
              L.obj ((shiftFunctor C m).obj
                ((shiftFunctor C (Additive.ofMul
                  (normalQuotientRepresentative N r.toMul))).obj X))) q
          (DirectSum.of
            (fun m : Additive N ↦
              L.obj ((shiftFunctor C m).obj
                ((shiftFunctor C (Additive.ofMul
                  (normalQuotientRepresentative N q.toMul))).obj X))) n
            (α.app ((shiftFunctor C n).obj
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X)) x))) =
      orbitPushdownNatTransAppLinear (A := Additive G) α X
        (D.residualOrbitPushdownValueLinearEquiv (M := M) N X
          (DirectSum.of
            (fun r : Additive (G ⧸ N) ↦
              DirectSum (Additive N) fun m ↦
                M.obj ((shiftFunctor C m).obj
                  ((shiftFunctor C (Additive.ofMul
                    (normalQuotientRepresentative N r.toMul))).obj X))) q
            (DirectSum.of
              (fun m : Additive N ↦
                M.obj ((shiftFunctor C m).obj
                  ((shiftFunctor C (Additive.ofMul
                    (normalQuotientRepresentative N q.toMul))).obj X))) n x)))
    rw [D.residualOrbitPushdownValueLinearEquiv_of_of,
      D.residualOrbitPushdownValueLinearEquiv_of_of]
    have hsource :
        DirectSum.of (fun g : Additive G ↦
            M.obj ((shiftFunctor C g).obj X))
            (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
            (D.residualPushdownHomogeneousLinearEquiv
              (M := M) N q n X x) =
          orbitPushdownLof M X
            (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
            (D.residualPushdownHomogeneousLinearEquiv
              (M := M) N q n X x) :=
      (orbitPushdownLof_eq_directSumOf M X
        (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
        (D.residualPushdownHomogeneousLinearEquiv
          (M := M) N q n X x)).symm
    rw [hsource, orbitPushdownNatTransAppLinear_lof]
    apply congrArg (orbitPushdownLof L X
      (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩))
    unfold residualPushdownHomogeneousLinearEquiv
    dsimp only [LinearEquiv.coe_coe, Functor.mapIso_hom]
    let a := Additive.ofMul (normalQuotientRepresentative N q.toMul)
    let b := Additive.ofMul (n.toMul : G)
    have hα :
        α.app ((shiftFunctor C b).obj ((shiftFunctor C a).obj X)) ≫
            L.map ((shiftFunctorAdd C a b).inv.app X) =
          M.map ((shiftFunctorAdd C a b).inv.app X) ≫
            α.app ((shiftFunctor C (a + b)).obj X) := by
      exact (α.naturality ((shiftFunctorAdd C a b).inv.app X)).symm
    exact congr($(hα) x)
  · intro z₁ z₂ hz₁ hz₂
    simpa only [map_add] using congrArg₂ (.+.) hz₁ hz₂

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
