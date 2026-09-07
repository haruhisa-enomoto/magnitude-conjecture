import MagnitudeConjecture.Algebra.RightModuleSupportWeakPositivity
import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundary
import MagnitudeConjecture.LinearAlgebra.UpperTriangularWeakPositivity

/-!
# Schurian boundary bounds

Weak positivity on the support of an indecomposable projective forces the
corresponding Cartan column to be thin.  This gives the projective half of
the schurian boundary estimate without importing a classification theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- Coordinates indexing a finite family of maps from `X` to the primitive
injectives selected by the complete idempotent presentation. -/
abbrev PrimitiveInjectiveCoordinateIndex
    (X : RightModule.FinitelyGeneratedCategory A) :=
  Σ p : S.ProjectiveLabel,
    Fin (Module.finrank k
      (RightModule.idempotentCoordinate (k := k) (P.idempotent p) X))

/-- The map to a primitive injective corresponding to one dual-basis
coordinate of `X e_p`. -/
def primitiveInjectiveCoordinateMap
    (X : RightModule.FinitelyGeneratedCategory A)
    (a : P.PrimitiveInjectiveCoordinateIndex X) :
    X ⟶ RightModule.primitiveInjectiveFGObj (k := k)
      (P.idempotent a.1) := by
  letI : Module.Finite k X :=
    RightModule.finite_over_field_of_finitelyGenerated k A X
  let V := RightModule.idempotentCoordinate (k := k)
    (P.idempotent a.1) X
  exact
    (RightModule.primitiveInjectiveHomCoordinateDualEquiv
        (k := k) (P.primitive a.1).idempotent X).symm
      ((Module.finBasis k V).coord a.2)

/-- The finite family of all primitive-injective coordinate maps. -/
def primitiveInjectiveEmbedding
    (X : RightModule.FinitelyGeneratedCategory A) :
    X ⟶ ⨁ fun a : P.PrimitiveInjectiveCoordinateIndex X ↦
      RightModule.primitiveInjectiveFGObj (k := k)
        (P.idempotent a.1) :=
  biproduct.lift (P.primitiveInjectiveCoordinateMap X)

/-- Completeness of the primitive idempotents makes the coordinate map a
monomorphism. -/
theorem primitiveInjectiveEmbedding_mono
    (X : RightModule.FinitelyGeneratedCategory A) :
    Mono (P.primitiveInjectiveEmbedding X) := by
  classical
  letI : Module.Finite k X :=
    RightModule.finite_over_field_of_finitelyGenerated k A X
  apply (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
    (P.primitiveInjectiveEmbedding X)).2
  intro x y hxy
  suffices hzero : x - y = 0 by exact sub_eq_zero.mp hzero
  have hall (p : S.ProjectiveLabel) :
      (MulOpposite.op (P.idempotent p)) • (x - y) = 0 := by
    let V := RightModule.idempotentCoordinate (k := k)
      (P.idempotent p) X
    let v : V := ⟨(MulOpposite.op (P.idempotent p)) • (x - y),
      ⟨x - y, rfl⟩⟩
    let b := Module.finBasis k V
    have hv : v = 0 := by
      apply b.ext_elem
      intro i
      let a : P.PrimitiveInjectiveCoordinateIndex X := ⟨p, i⟩
      let f := P.primitiveInjectiveCoordinateMap X a
      have hcomponent : f.hom.hom x = f.hom.hom y := by
        have hprojection :
            P.primitiveInjectiveEmbedding X ≫
                biproduct.π
                  (fun a : P.PrimitiveInjectiveCoordinateIndex X ↦
                    RightModule.primitiveInjectiveFGObj (k := k)
                      (P.idempotent a.1)) a = f := by
          simp [primitiveInjectiveEmbedding, f]
        have hxy' := congrArg
          (fun z ↦
            (biproduct.π
              (fun a : P.PrimitiveInjectiveCoordinateIndex X ↦
                RightModule.primitiveInjectiveFGObj (k := k)
                  (P.idempotent a.1)) a).hom.hom z) hxy
        change
          (P.primitiveInjectiveEmbedding X ≫
              biproduct.π
                (fun a : P.PrimitiveInjectiveCoordinateIndex X ↦
                  RightModule.primitiveInjectiveFGObj (k := k)
                    (P.idempotent a.1)) a).hom.hom x =
            (P.primitiveInjectiveEmbedding X ≫
              biproduct.π
                (fun a : P.PrimitiveInjectiveCoordinateIndex X ↦
                  RightModule.primitiveInjectiveFGObj (k := k)
                    (P.idempotent a.1)) a).hom.hom y at hxy'
        rw [hprojection] at hxy'
        exact hxy'
      have hfzero : f.hom.hom (x - y) = 0 := by
        rw [map_sub, hcomponent, sub_self]
      have hleftzero :
          (RightModule.primitiveInjectiveHomCoordinateDualEquiv
            (k := k) (P.primitive p).idempotent X) f v = 0 := by
        have hfv : f.hom.hom v.1 = 0 := by
          change f.hom.hom
            ((MulOpposite.op (P.idempotent p)) • (x - y)) = 0
          rw [f.hom.hom.map_smul, hfzero, smul_zero]
        exact
          RightModule.primitiveInjectiveHomCoordinateDualEquiv_apply_eq_zero
            (k := k) (P.primitive p).idempotent X f v hfv
      have happly' :
          (RightModule.primitiveInjectiveHomCoordinateDualEquiv
            (k := k) (P.primitive p).idempotent X) f v =
              b.coord i v := by
        have hfdef : f =
            (RightModule.primitiveInjectiveHomCoordinateDualEquiv
              (k := k) (P.primitive p).idempotent X).symm
                (b.coord i) := by
          rfl
        rw [hfdef, LinearEquiv.apply_symm_apply]
      rw [hleftzero] at happly'
      simpa [b.coord_apply] using happly'.symm
    exact congrArg Subtype.val hv
  calc
    x - y = (MulOpposite.op (1 : A)) • (x - y) := by simp
    _ = (MulOpposite.op (∑ p : S.ProjectiveLabel, P.idempotent p)) •
        (x - y) := by rw [P.complete.complete]
    _ = ∑ p : S.ProjectiveLabel,
        (MulOpposite.op (P.idempotent p)) • (x - y) := by
          rw [show MulOpposite.op
              (∑ p : S.ProjectiveLabel, P.idempotent p) =
                ∑ p : S.ProjectiveLabel,
                  MulOpposite.op (P.idempotent p) by simp,
            Finset.sum_smul]
    _ = 0 := Finset.sum_eq_zero fun p _ ↦ hall p

/-- Every selected indecomposable injective is one of the primitive
injectives belonging to the complete idempotent presentation. -/
theorem exists_iso_primitiveSink
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (i : S.InjectiveLabel) :
    ∃ p : S.ProjectiveLabel,
      Nonempty (S.fgObj i.label ≅
        S.fgObj (S.primitiveSinkLabel (P.primitive p))) := by
  classical
  let I := S.fgObj i.label
  let J := fun a : P.PrimitiveInjectiveCoordinateIndex I ↦
    RightModule.primitiveInjectiveFGObj (k := k) (P.idempotent a.1)
  let m : I ⟶ ⨁ J := P.primitiveInjectiveEmbedding I
  letI : Mono m := P.primitiveInjectiveEmbedding_mono I
  obtain ⟨r, hr⟩ := i.injective.factors (𝟙 I) m
  let f := fun a : P.PrimitiveInjectiveCoordinateIndex I ↦
    P.primitiveInjectiveCoordinateMap I a
  let g := fun a : P.PrimitiveInjectiveCoordinateIndex I ↦
    biproduct.ι J a ≫ r
  have hm : m = biproduct.lift f := by
    rfl
  have hrdesc : biproduct.desc g = r := by
    apply biproduct.hom_ext'
    intro a
    simp [g]
  have hsum : ∑ a, f a ≫ g a = 𝟙 I := by
    rw [← biproduct.lift_desc, ← hm, hrdesc]
    exact hr
  have hidne : (𝟙 I : I ⟶ I) ≠ 0 := by
    intro hid
    exact (S.fgObj_indecomposable i.label).1
      ((IsZero.iff_id_eq_zero I).2 hid)
  have hexists : ∃ a, f a ≫ g a ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hidne
    rw [← hsum]
    exact Finset.sum_eq_zero fun a _ ↦ hnone a
  obtain ⟨a, ha⟩ := hexists
  let c : I ⟶ I := f a ≫ g a
  letI : IsIso c := H.isIso_of_ne_zero_endomorphism S i.label c ha
  let r' : J a ⟶ I := g a ≫ inv c
  have hfr : f a ≫ r' = 𝟙 I := by
    change c ≫ inv c = 𝟙 I
    simp
  let d : J a ⟶ J a := r' ≫ f a
  let e := S.primitiveSinkIso (P.primitive a.1)
  let ds : S.fgObj (S.primitiveSinkLabel (P.primitive a.1)) ⟶
      S.fgObj (S.primitiveSinkLabel (P.primitive a.1)) :=
    e.inv ≫ d ≫ e.hom
  have hdne : d ≠ 0 := by
    intro hd
    have hfzero : f a = 0 := by
      calc
        f a = (f a ≫ r') ≫ f a := by rw [hfr, Category.id_comp]
        _ = f a ≫ d := by simp [d, Category.assoc]
        _ = 0 := by rw [hd, comp_zero]
    apply hidne
    rw [← hfr, hfzero, zero_comp]
  have hdsne : ds ≠ 0 := by
    intro hds
    apply hdne
    apply zero_of_comp_mono e.hom
    apply zero_of_epi_comp e.inv
    simpa [ds, Category.assoc] using hds
  letI : IsIso ds := H.isIso_of_ne_zero_endomorphism S
    (S.primitiveSinkLabel (P.primitive a.1)) ds hdsne
  have hdidem : d ≫ d = d := by
    calc
      d ≫ d = r' ≫ (f a ≫ r') ≫ f a := by
        simp [d, Category.assoc]
      _ = r' ≫ f a := by rw [hfr]; simp
      _ = d := rfl
  have hdsidem : ds ≫ ds = ds := by
    calc
      ds ≫ ds = e.inv ≫ (d ≫ d) ≫ e.hom := by
        simp [ds, Category.assoc]
      _ = ds := by rw [hdidem]
  have hdsone : ds = 𝟙 _ := by
    apply (cancel_epi ds).1
    simpa using hdsidem
  have hdone : d = 𝟙 _ := by
    calc
      d = e.hom ≫ ds ≫ e.inv := by simp [ds, Category.assoc]
      _ = e.hom ≫ 𝟙 _ ≫ e.inv := by rw [hdsone]
      _ = 𝟙 _ := by simp
  let fi : I ≅ J a :=
    { hom := f a
      inv := r'
      hom_inv_id := hfr
      inv_hom_id := hdone }
  exact ⟨a.1, ⟨fi.trans e⟩⟩

/-- Every Hom space between indecomposable projectives in a
representation-directed representation-finite algebra has dimension at most
one. -/
theorem projectiveHom_le_one
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p q : S.ProjectiveLabel) :
    Module.finrank k (S.fgObj p.label ⟶ S.fgObj q.label) ≤ 1 := by
  classical
  let X := S.fgObj q.label
  by_cases hp : p ∈ S.projectiveSupport X
  · let T := P.supportAlgebraSkeleton hA X
    let HT := P.supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms
      H hA X
    let w := P.supportLabel hA X X Set.Subset.rfl
      (S.obj_indecomposable q.label)
    have hwProjective : Projective (T.fgObj w) := by
      apply Projective.of_iso
        (P.supportFGObjIsoSkeletonFG hA X X Set.Subset.rfl
          (S.obj_indecomposable q.label))
      exact P.supportFGObj_projective X X Set.Subset.rfl q.projective
    let qt : T.ProjectiveLabel := ⟨w, hwProjective⟩
    let pt := P.supportProjectiveCoordinate hA X p hp
    let detection := P.supportLabel_sincereDetectionData hA X X
      Set.Subset.rfl (S.obj_indecomposable q.label) rfl
    have hweak := T.projectiveCartanInverse_weaklyPositive_of_sincereDetection
      HT w detection
    let D := T.supportWeaklyPositiveCartanData HT hweak
    letI := T.projectiveDirectedLinearOrder HT
    have hthin := D.entry_le_one_of_blockTriangular
      (T.projectiveCartanMatrix_blockTriangular HT) pt qt
    have hcoordinate := P.supportProjectiveHomVector_eq_ambient hA X
      q.label Set.Subset.rfl p hp
    change T.projectiveCartanMatrix pt qt ≤ 1 at hthin
    change (Module.finrank k
      (T.fgObj pt.label ⟶ T.fgObj w) : ℤ) ≤ 1 at hthin
    change (Module.finrank k
      (T.fgObj pt.label ⟶ T.fgObj w) : ℤ) =
        (Module.finrank k
          (S.fgObj p.label ⟶ S.fgObj q.label) : ℤ) at hcoordinate
    exact_mod_cast hcoordinate ▸ hthin
  · have hzero : ∀ f : S.fgObj p.label ⟶ S.fgObj q.label, f = 0 := by
      intro f
      by_contra hf
      exact hp ⟨f, hf⟩
    haveI : Subsingleton (S.fgObj p.label ⟶ S.fgObj q.label) :=
      ⟨fun f g ↦ (hzero f).trans (hzero g).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    omega

/-- Every Hom space between the literal primitive injectives has dimension
at most one.  Contragredient duality identifies it with the corresponding
primitive-projective corner. -/
theorem primitiveInjectiveHom_le_one
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p q : S.ProjectiveLabel) :
    Module.finrank k
      (RightModule.primitiveInjectiveFGObj (k := k) (P.idempotent p) ⟶
        RightModule.primitiveInjectiveFGObj (k := k) (P.idempotent q)) ≤ 1 := by
  rw [(RightModule.primitiveInjectiveHomRightIdealHomEquiv
    (k := k) (P.primitive p).idempotent
      (P.primitive q).idempotent).finrank_eq]
  have hpLabel :
      S.primitiveSourceLabel (P.primitive p) = p.label :=
    congrArg (fun r : S.ProjectiveLabel ↦ r.label) (P.sourceLabel p)
  have hqLabel :
      S.primitiveSourceLabel (P.primitive q) = q.label :=
    congrArg (fun r : S.ProjectiveLabel ↦ r.label) (P.sourceLabel q)
  rw [(CategoryTheory.Linear.homCongr k
    (S.primitiveSourceIso (P.primitive p))
      (S.primitiveSourceIso (P.primitive q))).finrank_eq]
  rw [hpLabel, hqLabel]
  exact P.projectiveHom_le_one hA H p q

/-- Every Hom space between the selected indecomposable injectives has
dimension at most one. -/
theorem injectiveHom_le_one
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (i j : S.InjectiveLabel) :
    Module.finrank k (S.fgObj i.label ⟶ S.fgObj j.label) ≤ 1 := by
  obtain ⟨p, ⟨ei⟩⟩ := exists_iso_primitiveSink (P := P) H i
  obtain ⟨q, ⟨ej⟩⟩ := exists_iso_primitiveSink (P := P) H j
  let ip : S.fgObj i.label ≅
      RightModule.primitiveInjectiveFGObj (k := k) (P.idempotent p) :=
    ei.trans (S.primitiveSinkIso (P.primitive p)).symm
  let jq : S.fgObj j.label ≅
      RightModule.primitiveInjectiveFGObj (k := k) (P.idempotent q) :=
    ej.trans (S.primitiveSinkIso (P.primitive q)).symm
  rw [(CategoryTheory.Linear.homCongr k ip jq).finrank_eq]
  exact primitiveInjectiveHom_le_one (P := P) hA H p q

/-- Representation-directedness constructs the complete schurian boundary
package used in Appendix A. -/
theorem schurianBoundaryData
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.SchurianBoundaryData where
  projectiveHom_le_one := P.projectiveHom_le_one hA H
  injectiveHom_le_one := injectiveHom_le_one (P := P) hA H

/-- The literal support quotients and the schurian corner theorem construct
the numerical coordinate estimate required by the primitive deletion. -/
theorem multiplicityCoordinateEstimate
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : RightModule.PrimitiveIdempotentData e) :
    S.MultiplicityCoordinateEstimate (S.primitiveMultiplicityInput D) :=
  MultiplicityCoordinateEstimate.ofMiddleSupport (S := S) D
    (P.middleSupportCartanData hA H D)
    (P.schurianBoundaryData hA H)

/-- The representation-directed hypotheses construct the complete boundary
data used by the primitive projective-poset realization. -/
theorem primitiveDirectedBoundaryData
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation)
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : RightModule.PrimitiveIdempotentData e) :
    S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D) :=
  PrimitiveDirectedBoundaryData.ofCoordinateEstimate (S := S)
    (S.primitiveMultiplicityInput D) H
      (P.multiplicityCoordinateEstimate hA H D)

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
