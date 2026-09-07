import MagnitudeConjecture.Algebra.RightModulePrimitiveTrace

/-!
# Ambient multiplicity data for a primitive deletion

The frozen manuscript uses one natural-valued function `d_X = [X:E]` on all
ambient indecomposable modules.  Its zero set is the killed subcategory, and
the projective cover and injective envelope identify it with both ambient Hom
dimensions.  This file proves that those ambient identities descend across
the literal factor and supply `PrimitiveTraceInput` automatically.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open scoped ModuleCat.Algebra ZeroObject

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Source-to-killed vanishing makes the quotient functor injective on every
ambient Hom space from the distinguished source. -/
theorem factorFunctor_map_injective_from
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (x : S.SurvivingLabel K) :
    Function.Injective
      ((S.factorFunctor K).map :
        (S.ambientAddPoint p.1 ⟶ S.ambientAddPoint x.1) →
          (S.factorObject K p ⟶ S.factorObject K x)) := by
  intro f g hfg
  rw [← sub_eq_zero]
  let I := S.factorThroughSelectedIdeal K
  have hmap : (S.factorFunctor K).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (f - g)).1 hmap
  have hleft : left = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsFromKilled hvanish hM left
  have hzero : f.hom - g.hom = 0 := by
    change left ≫ right = f.hom - g.hom at hfactor
    rw [hleft, zero_comp] at hfactor
    exact hfactor.symm
  apply ObjectProperty.hom_ext
  exact hzero

/-- Source-to-killed vanishing makes the quotient functor injective from the
distinguished source to every object of the ambient additive closure. -/
theorem factorFunctor_map_injective_from_object
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (X : S.SelectedAddCategory Set.univ) :
    Function.Injective
      ((S.factorFunctor K).map :
        (S.ambientAddPoint p.1 ⟶ X) →
          (S.factorObject K p ⟶ (S.factorFunctor K).obj X)) := by
  intro f g hfg
  rw [← sub_eq_zero]
  let I := S.factorThroughSelectedIdeal K
  have hmap : (S.factorFunctor K).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (f - g)).1 hmap
  have hleft : left = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsFromKilled hvanish hM left
  have hzero : f.hom - g.hom = 0 := by
    change left ≫ right = f.hom - g.hom at hfactor
    rw [hleft, zero_comp] at hfactor
    exact hfactor.symm
  apply ObjectProperty.hom_ext
  exact hzero

/-- Killed-to-sink vanishing makes the quotient functor injective on every
ambient Hom space into the distinguished sink. -/
theorem factorFunctor_map_injective_to
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (x : S.SurvivingLabel K) :
    Function.Injective
      ((S.factorFunctor K).map :
        (S.ambientAddPoint x.1 ⟶ S.ambientAddPoint i.1) →
          (S.factorObject K x ⟶ S.factorObject K i)) := by
  intro f g hfg
  rw [← sub_eq_zero]
  let I := S.factorThroughSelectedIdeal K
  have hmap : (S.factorFunctor K).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (f - g)).1 hmap
  have hright : right = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsToKilled hvanish hM right
  have hzero : f.hom - g.hom = 0 := by
    change left ≫ right = f.hom - g.hom at hfactor
    rw [hright, comp_zero] at hfactor
    exact hfactor.symm
  apply ObjectProperty.hom_ext
  exact hzero

/-- Killed-to-sink vanishing makes the quotient functor injective from every
object of the ambient additive closure to the distinguished sink. -/
theorem factorFunctor_map_injective_to_object
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (X : S.SelectedAddCategory Set.univ) :
    Function.Injective
      ((S.factorFunctor K).map :
        (X ⟶ S.ambientAddPoint i.1) →
          ((S.factorFunctor K).obj X ⟶ S.factorObject K i)) := by
  intro f g hfg
  rw [← sub_eq_zero]
  let I := S.factorThroughSelectedIdeal K
  have hmap : (S.factorFunctor K).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (f - g)).1 hmap
  have hright : right = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsToKilled hvanish hM right
  have hzero : f.hom - g.hom = 0 := by
    change left ≫ right = f.hom - g.hom at hfactor
    rw [hright, comp_zero] at hfactor
    exact hfactor.symm
  apply ObjectProperty.hom_ext
  exact hzero

/-- The quotient functor identifies the selected ambient source Hom space
with the corresponding factor Hom space. -/
def factorHomFromSelectedLinearEquiv
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (x : S.SurvivingLabel K) :
    (S.ambientAddPoint p.1 ⟶ S.ambientAddPoint x.1) ≃ₗ[k]
      (S.factorObject K p ⟶ S.factorObject K x) :=
  LinearEquiv.ofBijective
    ((S.factorFunctor K).mapLinearMap k)
    ⟨S.factorFunctor_map_injective_from hvanish x,
      (S.factorFunctor K).map_surjective⟩

/-- The quotient functor identifies Hom from the selected ambient source to
an arbitrary object of the ambient additive closure. -/
def factorHomFromSelectedObjectLinearEquiv
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (X : S.SelectedAddCategory Set.univ) :
    (S.ambientAddPoint p.1 ⟶ X) ≃ₗ[k]
      (S.factorObject K p ⟶ (S.factorFunctor K).obj X) :=
  LinearEquiv.ofBijective
    ((S.factorFunctor K).mapLinearMap k)
    ⟨S.factorFunctor_map_injective_from_object hvanish X,
      (S.factorFunctor K).map_surjective⟩

/-- The quotient functor identifies the selected ambient sink Hom space
with the corresponding factor Hom space. -/
def factorHomToSelectedLinearEquiv
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (x : S.SurvivingLabel K) :
    (S.ambientAddPoint x.1 ⟶ S.ambientAddPoint i.1) ≃ₗ[k]
      (S.factorObject K x ⟶ S.factorObject K i) :=
  LinearEquiv.ofBijective
    ((S.factorFunctor K).mapLinearMap k)
    ⟨S.factorFunctor_map_injective_to hvanish x,
      (S.factorFunctor K).map_surjective⟩

/-- The quotient functor identifies Hom from an arbitrary object of the
ambient additive closure to the selected ambient sink. -/
def factorHomToSelectedObjectLinearEquiv
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (X : S.SelectedAddCategory Set.univ) :
    (X ⟶ S.ambientAddPoint i.1) ≃ₗ[k]
      ((S.factorFunctor K).obj X ⟶ S.factorObject K i) :=
  LinearEquiv.ofBijective
    ((S.factorFunctor K).mapLinearMap k)
    ⟨S.factorFunctor_map_injective_to_object hvanish X,
      (S.factorFunctor K).map_surjective⟩

/-- Ambient finitely generated source Hom is linearly equivalent to factor
Hom. -/
def factorHomFromLinearEquiv
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (x : S.SurvivingLabel K) :
    (S.fgObj p.1 ⟶ S.fgObj x.1) ≃ₗ[k]
      (S.factorObject K p ⟶ S.factorObject K x) :=
  (InducedCategory.homLinearEquiv
    (R := k) (X := S.ambientAddPoint p.1)
      (Y := S.ambientAddPoint x.1)).symm.trans
    (S.factorHomFromSelectedLinearEquiv hvanish x)

/-- Ambient finitely generated Hom from the selected source is linearly
equivalent to factor Hom for an arbitrary finitely generated target. -/
def factorHomFromFGObjLinearEquiv
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.fgObj p.1 ⟶ X) ≃ₗ[k]
      (S.factorObject K p ⟶ (S.factorModuleFunctor K).obj X) :=
  (InducedCategory.homLinearEquiv
    (R := k) (X := S.ambientAddPoint p.1)
      (Y := S.ambientAddObject X)).symm.trans
    (S.factorHomFromSelectedObjectLinearEquiv hvanish
      (S.ambientAddObject X))

/-- Ambient finitely generated sink Hom is linearly equivalent to factor
Hom. -/
def factorHomToLinearEquiv
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (x : S.SurvivingLabel K) :
    (S.fgObj x.1 ⟶ S.fgObj i.1) ≃ₗ[k]
      (S.factorObject K x ⟶ S.factorObject K i) :=
  (InducedCategory.homLinearEquiv
    (R := k) (X := S.ambientAddPoint x.1)
      (Y := S.ambientAddPoint i.1)).symm.trans
    (S.factorHomToSelectedLinearEquiv hvanish x)

/-- Ambient finitely generated Hom to the selected sink is linearly
equivalent to factor Hom for an arbitrary finitely generated source. -/
def factorHomToFGObjLinearEquiv
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (X : RightModule.FinitelyGeneratedCategory A) :
    (X ⟶ S.fgObj i.1) ≃ₗ[k]
      ((S.factorModuleFunctor K).obj X ⟶ S.factorObject K i) :=
  (InducedCategory.homLinearEquiv
    (R := k) (X := S.ambientAddObject X)
      (Y := S.ambientAddPoint i.1)).symm.trans
    (S.factorHomToSelectedObjectLinearEquiv hvanish
      (S.ambientAddObject X))

/-- Exact ambient multiplicity data supplied by the projective cover and
injective envelope of the deleted simple. -/
structure PrimitiveMultiplicityInput (K : Set (Fin S.n)) where
  source : S.SurvivingLabel K
  sink : S.SurvivingLabel K
  source_projective : Projective (S.fgObj source.1)
  sink_injective : Injective (S.fgObj sink.1)
  multiplicity : Fin S.n → ℕ
  killed_iff_multiplicity_zero : ∀ x, x ∈ K ↔ multiplicity x = 0
  multiplicity_eq_sourceHom : ∀ x,
    multiplicity x = Module.finrank k (S.fgObj source.1 ⟶ S.fgObj x)
  multiplicity_eq_sinkHom : ∀ x,
    multiplicity x = Module.finrank k (S.fgObj x ⟶ S.fgObj sink.1)

/-- The ambient source Hom identity characterizes exactly the killed
labels. -/
theorem PrimitiveMultiplicityInput.killed_iff_sourceHomZero
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) (x : Fin S.n) :
    x ∈ K ↔ ∀ f : S.fgObj D.source.1 ⟶ S.fgObj x, f = 0 := by
  rw [D.killed_iff_multiplicity_zero x,
    D.multiplicity_eq_sourceHom x]
  exact finrank_zero_iff_forall_zero

/-- The ambient sink Hom identity characterizes exactly the killed labels.
-/
theorem PrimitiveMultiplicityInput.killed_iff_sinkHomZero
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) (x : Fin S.n) :
    x ∈ K ↔ ∀ f : S.fgObj x ⟶ S.fgObj D.sink.1, f = 0 := by
  rw [D.killed_iff_multiplicity_zero x,
    D.multiplicity_eq_sinkHom x]
  exact finrank_zero_iff_forall_zero

/-- The ambient multiplicity zero set gives source-to-killed vanishing. -/
theorem PrimitiveMultiplicityInput.noMapsFromKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    S.NoMapsFromKilled K D.source := by
  intro x hx f
  exact (PrimitiveMultiplicityInput.killed_iff_sourceHomZero
    (S := S) D x).1 hx f

/-- The ambient multiplicity zero set gives killed-to-sink vanishing. -/
theorem PrimitiveMultiplicityInput.noMapsToKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    S.NoMapsToKilled K D.sink := by
  intro x hx f
  exact (PrimitiveMultiplicityInput.killed_iff_sinkHomZero
    (S := S) D x).1 hx f

/-- The ambient multiplicity is strictly positive on every surviving
label. -/
theorem PrimitiveMultiplicityInput.multiplicity_pos
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) : 0 < D.multiplicity x.1 := by
  exact Nat.pos_of_ne_zero fun hzero ↦
    x.2 ((D.killed_iff_multiplicity_zero x.1).2 hzero)

/-- The ambient source multiplicity identity descends to the factor Hom
row. -/
theorem PrimitiveMultiplicityInput.weight_eq_from
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    (D.multiplicity x.1 : ℤ) =
      MagnitudeConjecture.FiniteTauMatrix.homFromWeight
        (k := k) (S.factorFiniteTauCategoryData K) D.source x := by
  change (D.multiplicity x.1 : ℤ) =
    (Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K x) : ℤ)
  exact_mod_cast (D.multiplicity_eq_sourceHom x.1).trans
    (S.factorHomFromLinearEquiv
      D.noMapsFromKilled x).finrank_eq

/-- The ambient sink multiplicity identity descends to the factor Hom
column. -/
theorem PrimitiveMultiplicityInput.weight_eq_to
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    (D.multiplicity x.1 : ℤ) =
      MagnitudeConjecture.FiniteTauMatrix.homToWeight
        (k := k) (S.factorFiniteTauCategoryData K) D.sink x := by
  change (D.multiplicity x.1 : ℤ) =
    (Module.finrank k
      (S.factorObject K x ⟶ S.factorObject K D.sink) : ℤ)
  exact_mod_cast (D.multiplicity_eq_sinkHom x.1).trans
    (S.factorHomToLinearEquiv
      D.noMapsToKilled x).finrank_eq

/-- Ambient multiplicity data supplies the complete trace-form primitive
input. -/
def PrimitiveMultiplicityInput.toPrimitiveTraceInput
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    S.PrimitiveTraceInput K where
  source := D.source
  sink := D.sink
  source_projective := D.source_projective
  sink_injective := D.sink_injective
  killed_iff_sourceHomZero := D.killed_iff_sourceHomZero
  killed_iff_sinkHomZero := D.killed_iff_sinkHomZero
  weight := fun x ↦ D.multiplicity x.1
  weight_pos := fun x ↦ by
    exact_mod_cast PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) D x
  weight_eq_from := D.weight_eq_from
  weight_eq_to := D.weight_eq_to

/-- Ambient multiplicity data gives strict factor meshes. -/
theorem PrimitiveMultiplicityInput.rightMesh_mono
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    Mono ((S.factorFiniteTauCategoryData K).rightMesh
      ((S.factorFiniteTauCategoryData K).obj x)).f :=
  PrimitiveTraceInput.rightMesh_mono
    (S := S) D.toPrimitiveTraceInput x

/-- Ambient multiplicity data gives strict factor left meshes. -/
theorem PrimitiveMultiplicityInput.leftMesh_epi
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    Epi ((S.factorFiniteTauCategoryData K).leftMesh
      ((S.factorFiniteTauCategoryData K).obj x)).g :=
  PrimitiveTraceInput.leftMesh_epi
    (S := S) D.toPrimitiveTraceInput x

/-- Over an algebraically closed field, ambient multiplicity data supplies
the complete Hom--mesh inverse package for the factor. -/
theorem PrimitiveMultiplicityInput.homMeshInverseData
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveMultiplicityInput K) :
    MagnitudeConjecture.FiniteTauMatrix.HomMeshInverseData
      (k := k) (S.factorFiniteTauCategoryData K) :=
  D.toPrimitiveTraceInput.homMeshInverseData

/-- Ambient multiplicity data gives both factor mesh unit equations. -/
theorem PrimitiveMultiplicityInput.meshUnitEquations
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveMultiplicityInput K) :
    (∀ target,
      MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight
          (S.factorFiniteTauCategoryData K)
          (fun x ↦ (D.multiplicity x.1 : ℤ)) target =
        if target = D.source then 1 else 0) ∧
      ∀ source,
        MagnitudeConjecture.FiniteTauMatrix.meshRowWeight
            (S.factorFiniteTauCategoryData K)
            (fun x ↦ (D.multiplicity x.1 : ℤ)) source =
          if source = D.sink then 1 else 0 :=
  D.toPrimitiveTraceInput.meshUnitEquations

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
