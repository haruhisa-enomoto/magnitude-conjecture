import MagnitudeConjecture.CategoryTheory.LinearCovering
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Pullback decompositions along a linear covering

Restriction of a covariant linear module along a linear functor is again a
linear module.  For a covering functor, the pullback of a representable is
the direct sum of the representables indexed by the fixed source fibre.

The fixed-fibre formulation is important: the indexing objects do not move
with the variable of the module, so the covering Hom equivalence is genuinely
natural without any choice of deck transformations.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.LinearCovering

universe u

variable {k : Type u} [Field k]

section DirectSumFiniteness

variable {ι : Type} (V : ι → Type u)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A finite-dimensional direct sum has only finitely many nontrivial
summands. -/
theorem finite_nontrivial_of_finiteDimensional_directSum
    [FiniteDimensional k (DirectSum ι V)] :
    {i : ι | Nontrivial (V i)}.Finite := by
  classical
  let S : Set ι := {i | Nontrivial (V i)}
  let x : ∀ i : S, V i.1 := fun i ↦ by
    letI : Nontrivial (V i.1) := i.2
    exact Classical.choose (exists_ne (0 : V i.1))
  have hx (i : S) : x i ≠ 0 := by
    letI : Nontrivial (V i.1) := i.2
    exact Classical.choose_spec (exists_ne (0 : V i))
  let v : S → DirectSum ι V := fun i ↦ DirectSum.of V i.1 (x i)
  have hv : LinearIndependent k v := by
    rw [linearIndependent_iff']
    intro s g h i hi
    have hcomp := congrArg (fun y : DirectSum ι V ↦ y i.1) h
    have hindex (j : S) : j.1 = i.1 ↔ j = i := by
      constructor
      · exact Subtype.ext
      · exact fun hji ↦ congrArg Subtype.val hji
    have hzero : g i • x i = 0 := by
      rw [DirectSum.sum_apply] at hcomp
      rw [Finset.sum_eq_single i] at hcomp
      · have hof : (DirectSum.of V i.1 (x i)) i.1 = x i := by
          simp
        change (g i • DirectSum.of V i.1 (x i)) i.1 = 0 at hcomp
        change g i • (DirectSum.of V i.1 (x i)) i.1 = 0 at hcomp
        rw [hof] at hcomp
        exact hcomp
      · intro j _hj hji
        have hval : j.1 ≠ i.1 := fun h ↦ hji ((hindex j).mp h)
        have hof : (DirectSum.of V j.1 (x j)) i.1 = 0 := by
          rw [DirectSum.of_apply]
          simp [hval]
        change (g j • DirectSum.of V j.1 (x j)) i.1 = 0
        change g j • (DirectSum.of V j.1 (x j)) i.1 = 0
        rw [hof, smul_zero]
      · intro hnot
        exact (hnot hi).elim
    exact (smul_eq_zero.mp hzero).resolve_right (hx i)
  letI : Finite S := hv.finite
  exact Set.toFinite _

/-- A direct sum indexed by an empty type has at most one element. -/
theorem directSum_subsingleton_of_not_nonempty
    (hι : ¬ Nonempty ι) : Subsingleton (DirectSum ι V) := by
  classical
  constructor
  intro a b
  have hzero (c : DirectSum ι V) : c = 0 := by
    induction c using DirectSum.induction_on with
    | zero => rfl
    | of i x => exact (hι ⟨i⟩).elim
    | add c d hc hd => simp only [hc, hd, add_zero]
  exact (hzero a).trans (hzero b).symm

end DirectSumFiniteness

variable {C D : Type} [Category.{u} C] [Category.{u} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k]

/-- If the target fibre is empty, every morphism from an object in the image
of a covering to that target is zero. -/
theorem IsCovering.targetHom_subsingleton_of_fiber_not_nonempty
    (hF : IsCovering (k := k) F) (X : C) (Y : D)
    (hY : ¬ Nonempty (Fiber F Y)) :
    Subsingleton (F.obj X ⟶ Y) :=
  (hF.targetFiberHomLinearEquiv X Y).toEquiv.subsingleton_congr.mp
    (directSum_subsingleton_of_not_nonempty
      (fun I : Fiber F Y ↦ X ⟶ I.1) hY)

/-- If the source fibre is empty, every morphism from that source to an
object in the image of a covering is zero. -/
theorem IsCovering.sourceHom_subsingleton_of_fiber_not_nonempty
    (hF : IsCovering (k := k) F) (X : D) (Y : C)
    (hX : ¬ Nonempty (Fiber F X)) :
    Subsingleton (X ⟶ F.obj Y) :=
  (hF.sourceFiberHomLinearEquiv X Y).toEquiv.subsingleton_congr.mp
    (directSum_subsingleton_of_not_nonempty
      (fun I : Fiber F X ↦ I.1 ⟶ Y) hX)

/-- Restriction of a covariant linear module along a linear functor. -/
noncomputable def linearModulePullback
    (M : CoveringHom.LinearModuleCategory (C := D) k) :
    CoveringHom.LinearModuleCategory (C := C) k :=
  ⟨F ⋙ M.obj, inferInstance, inferInstance⟩

/-- Restriction along a linear functor preserves isomorphisms of linear
modules. -/
noncomputable def linearModulePullbackIso
    {M N : CoveringHom.LinearModuleCategory (C := D) k}
    (e : M ≅ N) :
    linearModulePullback (k := k) F M ≅
      linearModulePullback (k := k) F N :=
  ObjectProperty.isoMk (P := CoveringHom.IsLinearModule (C := C) k)
    (Functor.isoWhiskerLeft F
      ((CoveringHom.IsLinearModule (C := D) k).ι.mapIso e))

/-- The fixed-source-fibre direct sum of representables.  At `Y` its value is
`⨁_(P in F⁻¹(X)) Hom(P,Y)`. -/
noncomputable def sourceFiberRepresentableSum (X : D) :
    C ⥤ ModuleCat k where
  obj Y := ModuleCat.of k
    (DirectSum (Fiber F X) (fun P ↦ P.1 ⟶ Y))
  map {Y Z} f := ModuleCat.ofHom
    (sourceFiberPostcomp (k := k) F X f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply DirectSum.ext
    intro P
    simp
  map_comp {Y Z W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (sourceFiberPostcomp_comp (k := k) F X f g a).symm

instance sourceFiberRepresentableSum_additive (X : D) :
    (sourceFiberRepresentableSum (k := k) F X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change sourceFiberPostcomp (k := k) F X (f + g) a =
      sourceFiberPostcomp (k := k) F X f a +
        sourceFiberPostcomp (k := k) F X g a
    apply DirectSum.ext
    intro P
    simp

instance sourceFiberRepresentableSum_linear (X : D) :
    (sourceFiberRepresentableSum (k := k) F X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change DirectSum (Fiber F X) (fun P ↦ P.1 ⟶ _) at a
    change sourceFiberPostcomp (k := k) F X (r • f) a =
      r • sourceFiberPostcomp (k := k) F X f a
    apply DirectSum.ext
    intro P
    rw [sourceFiberPostcomp_apply]
    change a P ≫ (r • f) =
      r • ((sourceFiberPostcomp (k := k) F X f a) P)
    rw [sourceFiberPostcomp_apply]
    exact CategoryTheory.Linear.comp_smul _ _ _ (a P) r f

/-- The fixed-source-fibre sum, bundled in the category of linear modules. -/
noncomputable def sourceFiberRepresentableLinearModule (X : D) :
    CoveringHom.LinearModuleCategory (C := C) k :=
  ⟨sourceFiberRepresentableSum (k := k) F X, inferInstance, inferInstance⟩

/-- Include one representable indexed by the fixed source fibre into the
direct-sum module. -/
noncomputable def sourceFiberRepresentableInclusion
    (X : D) (P : Fiber F X) :
    CoveringHom.linearCoyonedaLinearModule (k := k) P.1 ⟶
      sourceFiberRepresentableLinearModule (k := k) F X :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom
        (sourceFiberLof (k := k) F X Y P)
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        exact (sourceFiberPostcomp_lof (k := k) F X f P q).symm }

/-- Project the fixed-source direct-sum module onto one representable
summand. -/
noncomputable def sourceFiberRepresentableProjection
    (X : D) (P : Fiber F X) :
    sourceFiberRepresentableLinearModule (k := k) F X ⟶
      CoveringHom.linearCoyonedaLinearModule (k := k) P.1 :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom
        (DirectSum.component k (Fiber F X) (fun Q ↦ Q.1 ⟶ Y) P)
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact sourceFiberPostcomp_apply (k := k) F X f a P }

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
@[reassoc]
theorem sourceFiberRepresentableInclusion_projection
    (X : D) (P : Fiber F X) :
    sourceFiberRepresentableInclusion (k := k) F X P ≫
        sourceFiberRepresentableProjection (k := k) F X P =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change DirectSum.component k (Fiber F X) (fun Q ↦ Q.1 ⟶ Y) P
      (sourceFiberLof (k := k) F X Y P q) = q
  simp [sourceFiberLof]

/-- A covering identifies the fixed-source-fibre representable sum with the
pullback of the downstairs representable. -/
noncomputable def sourceFiberRepresentablePullbackIso
    (hF : IsCovering (k := k) F) (X : D) :
    sourceFiberRepresentableLinearModule (k := k) F X ≅
      linearModulePullback (k := k) F
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦
    (hF.sourceFiberHomLinearEquiv X Y).toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact sourceFiberHomMap_sourceFiberPostcomp (k := k) F X f a

/-- On the duals of the fixed-target-fibre Hom spaces, a morphism acts
componentwise by dualized precomposition. -/
def targetFiberDualMap (X : D) {Y Z : C} (f : Y ⟶ Z) :
    DirectSum (Fiber F X)
        (fun J ↦ Module.Dual k (Y ⟶ J.1)) →ₗ[k]
      DirectSum (Fiber F X)
        (fun J ↦ Module.Dual k (Z ⟶ J.1)) :=
  DirectSum.lmap fun J ↦
    (CategoryTheory.Linear.leftComp k J.1 f).dualMap

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
@[simp]
theorem targetFiberDualMap_apply
    (X : D) {Y Z : C} (f : Y ⟶ Z)
    (a : DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (Y ⟶ J.1)))
    (J : Fiber F X) :
    targetFiberDualMap (k := k) F X f a J =
      (CategoryTheory.Linear.leftComp k J.1 f).dualMap (a J) :=
  rfl

/-- The fixed-target-fibre direct sum of dual corepresentables.  At `Y` its
value is `⨁_(J in F⁻¹(X)) D Hom(Y,J)`. -/
noncomputable def targetFiberDualCorepresentableSum (X : D) :
    C ⥤ ModuleCat k where
  obj Y := ModuleCat.of k
    (DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (Y ⟶ J.1)))
  map {Y Z} f := ModuleCat.ofHom (targetFiberDualMap (k := k) F X f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply DirectSum.ext
    intro J
    apply LinearMap.ext
    intro q
    simp [targetFiberDualMap]
  map_comp {Y Z W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply DirectSum.ext
    intro J
    apply LinearMap.ext
    intro q
    simp [targetFiberDualMap, Category.assoc]

instance targetFiberDualCorepresentableSum_additive (X : D) :
    (targetFiberDualCorepresentableSum (k := k) F X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (_ ⟶ J.1)) at a
    change targetFiberDualMap (k := k) F X (f + g) a =
      targetFiberDualMap (k := k) F X f a +
        targetFiberDualMap (k := k) F X g a
    apply DirectSum.ext
    intro J
    apply LinearMap.ext
    intro q
    simp [Preadditive.add_comp]

instance targetFiberDualCorepresentableSum_linear (X : D) :
    (targetFiberDualCorepresentableSum (k := k) F X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (_ ⟶ J.1)) at a
    change targetFiberDualMap (k := k) F X (r • f) a =
      r • targetFiberDualMap (k := k) F X f a
    apply DirectSum.ext
    intro J
    apply LinearMap.ext
    intro q
    change a J ((r • f) ≫ q) = r • (a J (f ≫ q))
    rw [CategoryTheory.Linear.smul_comp]
    exact map_smul (a J) r (f ≫ q)

/-- The fixed-target-fibre dual-corepresentable sum, bundled as a linear
module. -/
noncomputable def targetFiberDualCorepresentableLinearModule (X : D) :
    CoveringHom.LinearModuleCategory (C := C) k :=
  ⟨targetFiberDualCorepresentableSum (k := k) F X,
    inferInstance, inferInstance⟩

/-- Include one dual corepresentable indexed by the fixed target fibre into
the direct-sum module. -/
noncomputable def targetFiberDualCorepresentableInclusion
    (X : D) (J : Fiber F X) :
    CoveringHom.dualLinearYonedaLinearModule (k := k) J.1 ⟶
      targetFiberDualCorepresentableLinearModule (k := k) F X := by
  classical
  apply ObjectProperty.homMk
  refine
    { app := fun Y ↦ ModuleCat.ofHom
        (DirectSum.lof k (Fiber F X)
          (fun L ↦ Module.Dual k (Y ⟶ L.1)) J)
      naturality := ?_ }
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change DirectSum.of
      (fun L : Fiber F X ↦ Module.Dual k (Z ⟶ L.1)) J
        ((CategoryTheory.Linear.leftComp k J.1 f).dualMap phi) =
    targetFiberDualMap (k := k) F X f
      (DirectSum.of
        (fun L : Fiber F X ↦ Module.Dual k (Y ⟶ L.1)) J phi)
  apply DirectSum.ext
  intro L
  rw [targetFiberDualMap_apply]
  by_cases hJL : J = L
  · subst L
    simp
  · simp [DirectSum.of_apply, hJL]

/-- Project the fixed-target direct-sum module onto one dual
corepresentable summand. -/
noncomputable def targetFiberDualCorepresentableProjection
    (X : D) (J : Fiber F X) :
    targetFiberDualCorepresentableLinearModule (k := k) F X ⟶
      CoveringHom.dualLinearYonedaLinearModule (k := k) J.1 := by
  classical
  apply ObjectProperty.homMk
  exact
    { app := fun Y ↦ ModuleCat.ofHom
        (DirectSum.component k (Fiber F X)
          (fun L ↦ Module.Dual k (Y ⟶ L.1)) J)
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        rfl }

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
@[reassoc]
theorem targetFiberDualCorepresentableInclusion_projection
    (X : D) (J : Fiber F X) :
    targetFiberDualCorepresentableInclusion (k := k) F X J ≫
        targetFiberDualCorepresentableProjection (k := k) F X J =
      𝟙 _ := by
  classical
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change DirectSum.component k (Fiber F X)
      (fun L ↦ Module.Dual k (Y ⟶ L.1)) J
      (DirectSum.of (fun L ↦ Module.Dual k (Y ⟶ L.1)) J phi) = phi
  rw [← DirectSum.lof_eq_of k (Fiber F X)
    (fun L ↦ Module.Dual k (Y ⟶ L.1)) J phi,
    DirectSum.component.lof_self]

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
/-- The covering-specific inclusion agrees with the canonical direct-sum
inclusion, independently of the hidden decidable-equality choice. -/
theorem targetFiberLof_eq_directSumInclusion
    (X : C) (Y : D) (J : Fiber F Y) :
    targetFiberLof (k := k) F X Y J =
      directSumInclusion (k := k)
        (fun L : Fiber F Y ↦ X ⟶ L.1) J := by
  classical
  apply LinearMap.ext
  intro q
  apply DirectSum.ext
  intro L
  by_cases hJL : J = L
  · subst L
    simp [targetFiberLof, directSumInclusion]
  · simp [targetFiberLof, directSumInclusion,
      DirectSum.lof_eq_of, DirectSum.of_apply, hJL]

/-- Pointwise, finite direct-sum duality followed by the dual covering Hom
equivalence identifies the fixed-target sum with the dual Hom space
downstairs. -/
noncomputable def targetFiberDualCorepresentableValueEquiv
    (hF : IsCovering (k := k) F) (X : D) (Y : C)
    (hfinite : {J : Fiber F X | Nontrivial (Y ⟶ J.1)}.Finite) :
    DirectSum (Fiber F X)
        (fun J ↦ Module.Dual k (Y ⟶ J.1)) ≃ₗ[k]
      Module.Dual k (F.obj Y ⟶ X) :=
  (directSumDualEquivDual (k := k)
      (fun J : Fiber F X ↦ Y ⟶ J.1) hfinite).trans
    (hF.targetFiberHomLinearEquiv Y X).dualMap.symm

@[simp]
theorem targetFiberDualCorepresentableValueEquiv_apply
    (hF : IsCovering (k := k) F) (X : D) (Y : C)
    (hfinite : {J : Fiber F X | Nontrivial (Y ⟶ J.1)}.Finite)
    (a : DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (Y ⟶ J.1)))
    (q : F.obj Y ⟶ X) :
    targetFiberDualCorepresentableValueEquiv
        (k := k) F hF X Y hfinite a q =
      directSumDualToDual (k := k)
        (fun J : Fiber F X ↦ Y ⟶ J.1) a
        ((hF.targetFiberHomLinearEquiv Y X).symm q) :=
  rfl

/-- The inverse covering Hom equivalences commute with precomposition. -/
theorem targetFiberHomLinearEquiv_symm_comp
    (hF : IsCovering (k := k) F) (X : D)
    {Y Z : C} (f : Y ⟶ Z) (q : F.obj Z ⟶ X) :
    (hF.targetFiberHomLinearEquiv Y X).symm (F.map f ≫ q) =
      targetFiberPrecomp (k := k) F X f
        ((hF.targetFiberHomLinearEquiv Z X).symm q) := by
  apply (hF.targetFiberHomLinearEquiv Y X).injective
  rw [LinearEquiv.apply_symm_apply]
  change F.map f ≫ q =
    targetFiberHomMap (k := k) F Y X
      (targetFiberPrecomp (k := k) F X f
        ((hF.targetFiberHomLinearEquiv Z X).symm q))
  rw [targetFiberHomMap_targetFiberPrecomp]
  change F.map f ≫ q =
    F.map f ≫
      hF.targetFiberHomLinearEquiv Z X
        ((hF.targetFiberHomLinearEquiv Z X).symm q)
  rw [LinearEquiv.apply_symm_apply]

omit [Preadditive D] [CategoryTheory.Linear k D]
  [F.Additive] [F.Linear k] in
/-- Componentwise dualized precomposition is adjoint to precomposition on
the fixed-target Hom direct sum under the canonical direct-sum pairing. -/
theorem targetFiberDualMap_pairing
    (X : D) {Y Z : C} (f : Y ⟶ Z)
    (a : DirectSum (Fiber F X)
      (fun J ↦ Module.Dual k (Y ⟶ J.1)))
    (b : DirectSum (Fiber F X) (fun J ↦ Z ⟶ J.1)) :
    directSumDualToDual (k := k)
        (fun J : Fiber F X ↦ Z ⟶ J.1)
        (targetFiberDualMap (k := k) F X f a) b =
      directSumDualToDual (k := k)
        (fun J : Fiber F X ↦ Y ⟶ J.1) a
        (targetFiberPrecomp (k := k) F X f b) := by
  classical
  induction b using DirectSum.induction_on with
  | zero => simp
  | of J q =>
      rw [← DirectSum.lof_eq_of k (Fiber F X)
        (fun L ↦ Z ⟶ L.1) J q]
      change directSumDualToDual (k := k)
          (fun L : Fiber F X ↦ Z ⟶ L.1)
          (targetFiberDualMap (k := k) F X f a)
          (targetFiberLof (k := k) F Z X J q) =
        directSumDualToDual (k := k)
          (fun L : Fiber F X ↦ Y ⟶ L.1) a
          (targetFiberPrecomp (k := k) F X f
            (targetFiberLof (k := k) F Z X J q))
      rw [targetFiberPrecomp_lof]
      rw [targetFiberLof_eq_directSumInclusion,
        targetFiberLof_eq_directSumInclusion,
        directSumDualToDual_apply_lof,
        directSumDualToDual_apply_lof,
        targetFiberDualMap_apply, LinearMap.dualMap_apply]
      rfl
  | add b c hb hc =>
      simp only [map_add, hb, hc]

/-- A covering identifies the fixed-target-fibre sum of dual
corepresentables with the pullback of the downstairs dual corepresentable. -/
noncomputable def targetFiberDualCorepresentablePullbackIso
    (hF : IsCovering (k := k) F) (X : D)
    (hfinite : ∀ Y : C,
      {J : Fiber F X | Nontrivial (Y ⟶ J.1)}.Finite) :
    targetFiberDualCorepresentableLinearModule (k := k) F X ≅
      linearModulePullback (k := k) F
        (CoveringHom.dualLinearYonedaLinearModule (k := k) X) := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦
    (targetFiberDualCorepresentableValueEquiv
      (k := k) F hF X Y (hfinite Y)).toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change DirectSum (Fiber F X)
    (fun J ↦ Module.Dual k (Y ⟶ J.1)) at a
  apply LinearMap.ext
  intro q
  change targetFiberDualCorepresentableValueEquiv
      (k := k) F hF X Z (hfinite Z)
        (targetFiberDualMap (k := k) F X f a) q =
    targetFiberDualCorepresentableValueEquiv
      (k := k) F hF X Y (hfinite Y) a (F.map f ≫ q)
  rw [targetFiberDualCorepresentableValueEquiv_apply,
    targetFiberDualCorepresentableValueEquiv_apply,
    targetFiberHomLinearEquiv_symm_comp]
  exact targetFiberDualMap_pairing (k := k) F X f a
    ((hF.targetFiberHomLinearEquiv Z X).symm q)

end MagnitudeConjecture.LinearCovering
