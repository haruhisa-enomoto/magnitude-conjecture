import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.HomInteractionSeparation
import MagnitudeConjecture.CategoryTheory.IrreducibleFiniteCoreFunctor
import MagnitudeConjecture.Combinatorics.FiniteInteractionNeighborhood
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite module control windows up to isomorphism

Local representation-finiteness makes the symmetric Hom neighborhood of an
indecomposable finite module finite up to isomorphism.  Iterating this
construction gives the manuscript's finite three-step control window.  The
actual set-valued window is the isomorphism closure of a finite family; this
distinguishes correctly between finiteness of indecomposable isomorphism
classes and literal finiteness of the ambient type of module objects.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [CategoryTheory.Linear k C]

abbrev ControlFiniteModule (k : Type v) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C]
    [CategoryTheory.Linear k C] :=
  FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k

/-- Isomorphic finite-dimensional modules have the same literal object
support. -/
theorem mem_moduleSupport_iff_of_iso
    {M N : ControlFiniteModule k C} (e : M ≅ N) (X : C) :
    X ∈ moduleSupport k M.obj.obj ↔
      X ∈ moduleSupport k N.obj.obj := by
  let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  let eX := (J.mapIso
    ((IsFiniteDimensionalModule (C := C) k).ι.mapIso e)).app X
  exact eX.toLinearEquiv.toEquiv.nontrivial_congr

/-- A nonzero morphism of finite modules has a base object at which both its
source and target are nonzero. -/
theorem exists_common_moduleSupport_of_ne_zero
    {M N : ControlFiniteModule k C} (f : M ⟶ N) (hf : f ≠ 0) :
    ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k N.obj.obj := by
  have hcomponent : ∃ X : C, f.hom.hom.app X ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact hall X
  obtain ⟨X, hX⟩ := hcomponent
  have hMX : Nontrivial (M.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim _ _]
    simp
  have hNX : Nontrivial (N.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  exact ⟨X, hMX, hNX⟩

/-- A finite list representing every indecomposable module in the symmetric
Hom neighborhood of `M`. -/
structure FiniteIndecomposableHomNeighborhood (M : ControlFiniteModule k C) where
  n : ℕ
  obj : Fin n → ControlFiniteModule k C
  indecomposable : ∀ i, Indecomposable (obj i)
  covers : ∀ {Y : ControlFiniteModule k C}, Indecomposable Y →
    CoveringSeparation.homInteraction M Y →
      ∃ i, Nonempty (obj i ≅ Y)

/-- The interaction relation on the indecomposable vertices of the module
category.  The indecomposability guard is essential: the manuscript's finite
windows are windows in `ind(mod C)`, not literally finite subsets of all
module objects. -/
def indecomposableHomInteraction (M Y : ControlFiniteModule k C) : Prop :=
  Indecomposable Y ∧ CoveringSeparation.homInteraction M Y

/-- Local representation-finiteness supplies a finite symmetric Hom
neighborhood for every indecomposable finite module. -/
def finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : ControlFiniteModule k C) (hM : Indecomposable M) :
    FiniteIndecomposableHomNeighborhood (k := k) M := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let H (X : S) := Classical.choice (hlocal X.1)
  let I := Σ X : S,
    {j : Fin (H X).n // Nontrivial (((H X).obj j).obj.obj.obj X.1)}
  letI : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  refine
    { n := n
      obj := fun t ↦ (H (e t).1).obj (e t).2.1
      indecomposable := fun t ↦ (H (e t).1).indecomposable (e t).2.1
      covers := ?_ }
  intro Y hY hMY
  have hcommon : ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k Y.obj.obj := by
    rcases hMY with hEq | hforward | hbackward
    · subst Y
      have hid : (𝟙 M : M ⟶ M) ≠ 0 := by
        intro hid
        exact hM.1 ((Limits.IsZero.iff_id_eq_zero M).2 hid)
      exact exists_common_moduleSupport_of_ne_zero (𝟙 M) hid
    · letI := hforward
      obtain ⟨f, hf⟩ := exists_ne (0 : M ⟶ Y)
      exact exists_common_moduleSupport_of_ne_zero f hf
    · letI := hbackward
      obtain ⟨f, hf⟩ := exists_ne (0 : Y ⟶ M)
      obtain ⟨X, hYX, hMX⟩ :=
        exists_common_moduleSupport_of_ne_zero f hf
      exact ⟨X, hMX, hYX⟩
  obtain ⟨X, hMX, hYX⟩ := hcommon
  let Xs : S := ⟨X, hMX⟩
  obtain ⟨j, hj⟩ := (H Xs).covers hY hYX
  have hjX : Nontrivial (((H Xs).obj j).obj.obj.obj X) := by
    let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    let eX := (J.mapIso
      ((IsFiniteDimensionalModule (C := C) k).ι.mapIso
        (Classical.choice hj))).app X
    exact eX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hYX
  let p : I := ⟨Xs, ⟨j, hjX⟩⟩
  refine ⟨e.symm p, ?_⟩
  change Nonempty
    ((H (e (e.symm p)).1).obj (e (e.symm p)).2.1 ≅ Y)
  rw [e.apply_symm_apply p]
  exact hj

/-- Every representative chosen in a finite Hom neighborhood genuinely
shares an object-support point with the center module. -/
theorem finiteIndecomposableHomNeighborhood_obj_commonSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : ControlFiniteModule k C) (hM : Indecomposable M)
    (t : Fin
      (finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
        hlocal M hM).n) :
    ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k
          ((finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
            hlocal M hM).obj t).obj.obj := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let H (X : S) := Classical.choice (hlocal X.1)
  let I := Σ X : S,
    {j : Fin (H X).n // Nontrivial (((H X).obj j).obj.obj.obj X.1)}
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨(e t).1.1, (e t).1.2, ?_⟩
  change Nontrivial (((H (e t).1).obj (e t).2.1).obj.obj.obj (e t).1.1)
  exact (e t).2.property

/-- Every indecomposable sharing an object-support point with the center is
represented in its finite Hom neighborhood. -/
theorem finiteIndecomposableHomNeighborhood_covers_commonSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : ControlFiniteModule k C) (hM : Indecomposable M)
    {Y : ControlFiniteModule k C} (hY : Indecomposable Y)
    (hcommon : ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k Y.obj.obj) :
    ∃ t, Nonempty
      ((finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
        hlocal M hM).obj t ≅ Y) := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let H (X : S) := Classical.choice (hlocal X.1)
  let I := Σ X : S,
    {j : Fin (H X).n // Nontrivial (((H X).obj j).obj.obj.obj X.1)}
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨X, hMX, hYX⟩ := hcommon
  let Xs : S := ⟨X, hMX⟩
  obtain ⟨j, ⟨q⟩⟩ := (H Xs).covers hY hYX
  have hjX : Nontrivial (((H Xs).obj j).obj.obj.obj X) := by
    let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    let qX := (J.mapIso
      ((IsFiniteDimensionalModule (C := C) k).ι.mapIso q)).app X
    exact qX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hYX
  let p : I := ⟨Xs, ⟨j, hjX⟩⟩
  refine ⟨e.symm p, ?_⟩
  change Nonempty
    ((H (e (e.symm p)).1).obj (e (e.symm p)).2.1 ≅ Y)
  rw [e.apply_symm_apply p]
  exact ⟨q⟩

/-- A finite family of chosen indecomposable module representatives. -/
structure FiniteIndecomposableModuleFamily where
  n : ℕ
  obj : Fin n → ControlFiniteModule k C
  indecomposable : ∀ i, Indecomposable (obj i)

/-- Forget the coverage property of a pointwise local-representation-finite
fiber and retain its finite family of indecomposable representatives. -/
def FiniteIndecomposableFiber.toModuleFamily
    {X : C} (H : FiniteIndecomposableFiber (k := k) X) :
    FiniteIndecomposableModuleFamily (k := k) (C := C) where
  n := H.n
  obj := H.obj
  indecomposable := H.indecomposable

namespace FiniteIndecomposableModuleFamily

variable (S : FiniteIndecomposableModuleFamily (k := k) (C := C))

/-- Restrict a finite representative family to a finite set of its indices. -/
def subfamily (I : Finset (Fin S.n)) :
    FiniteIndecomposableModuleFamily (k := k) (C := C) :=
  let e : Fin I.card ≃ I := I.equivFin.symm
  { n := I.card
    obj := fun t ↦ S.obj (e t).1
    indecomposable := fun t ↦ S.indecomposable (e t).1 }

/-- Flatten a finite family of finite representative families. -/
def flatten {ι : Type} [Fintype ι]
    (W : ι → FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    FiniteIndecomposableModuleFamily (k := k) (C := C) :=
  let I := Σ i : ι, Fin (W i).n
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  { n := Fintype.card I
    obj := fun t ↦ (W (e t).1).obj (e t).2
    indecomposable := fun t ↦ (W (e t).1).indecomposable (e t).2 }

/-- The set-valued control window represented by a finite family: all module
objects isomorphic to one of its chosen representatives. -/
def isoClosure : Set (ControlFiniteModule k C) :=
  {M | ∃ i, Nonempty (S.obj i ≅ M)}

/-- A selected parent representative belongs to the isomorphism closure of
the corresponding finite subfamily. -/
theorem obj_mem_subfamily_isoClosure
    (I : Finset (Fin S.n)) {i : Fin S.n} (hi : i ∈ I) :
    S.obj i ∈ (S.subfamily I).isoClosure := by
  let ii : I := ⟨i, hi⟩
  refine ⟨I.equivFin ii, ?_⟩
  change Nonempty (S.obj (I.equivFin.symm (I.equivFin ii)).1 ≅ S.obj i)
  rw [I.equivFin.symm_apply_apply]
  exact ⟨Iso.refl _⟩

/-- Every member of one constituent family belongs to the isomorphism
closure of the flattened finite family. -/
theorem isoClosure_subset_flatten
    {ι : Type} [Fintype ι]
    (W : ι → FiniteIndecomposableModuleFamily (k := k) (C := C))
    (i : ι) :
    (W i).isoClosure ⊆ (flatten W).isoClosure := by
  intro M hM
  obtain ⟨j, ⟨eM⟩⟩ := hM
  let p : Σ i : ι, Fin (W i).n := ⟨i, j⟩
  let e : Fin (Fintype.card (Σ i : ι, Fin (W i).n)) ≃
      (Σ i : ι, Fin (W i).n) :=
    (Fintype.equivFin (Σ i : ι, Fin (W i).n)).symm
  refine ⟨e.symm p, ?_⟩
  change Nonempty ((W (e (e.symm p)).1).obj (e (e.symm p)).2 ≅ M)
  rw [e.apply_symm_apply]
  exact ⟨eM⟩

/-- The additive hull generated by the finite indecomposable family: objects
isomorphic to finite biproducts of its members, with repetitions allowed.
This is the categorical window in which arbitrary relevant factorization
cores live. -/
def additiveClosure : Set (ControlFiniteModule k C) :=
  {M | ∃ (n : ℕ) (label : Fin n → Fin S.n),
    Nonempty ((⨁ fun j ↦ S.obj (label j)) ≅ M)}

/-- The literal range of chosen representatives is finite. -/
theorem range_finite : (Set.range S.obj).Finite :=
  Set.finite_range S.obj

/-- Every chosen representative belongs to the isomorphism closure. -/
theorem obj_mem_isoClosure (i : Fin S.n) : S.obj i ∈ S.isoClosure :=
  ⟨i, ⟨Iso.refl _⟩⟩

/-- The indecomposable isomorphism closure embeds in the additive hull. -/
theorem isoClosure_subset_additiveClosure : S.isoClosure ⊆ S.additiveClosure := by
  intro M hM
  obtain ⟨i, ⟨e⟩⟩ := hM
  refine ⟨1, fun _ ↦ i, ⟨?_⟩⟩
  exact biproductUniqueIso (fun _ : Fin 1 ↦ S.obj i) ≪≫ e

/-- The additive hull is closed under isomorphism. -/
instance additiveClosure_isClosedUnderIsomorphisms :
    (show ObjectProperty (ControlFiniteModule k C) from S.additiveClosure).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    obtain ⟨n, label, ⟨d⟩⟩ := hM
    exact ⟨n, label, ⟨d ≪≫ e⟩⟩

/-- The additive hull contains a zero object, represented by the empty
biproduct. -/
instance additiveClosure_containsZero :
    (show ObjectProperty (ControlFiniteModule k C) from S.additiveClosure).ContainsZero where
  exists_zero := by
    let Z : ControlFiniteModule k C :=
      ⨁ fun j : Fin 0 ↦ S.obj (Fin.elim0 j)
    have hZ : IsZero Z :=
      { unique_to := fun Y ↦ ⟨
          { default := 0
            uniq := fun f ↦ by
              apply biproduct.hom_ext'
              intro j
              exact Fin.elim0 j }⟩
        unique_from := fun Y ↦ ⟨
          { default := 0
            uniq := fun f ↦ by
              apply biproduct.hom_ext
              intro j
              exact Fin.elim0 j }⟩ }
    exact ⟨Z, hZ, 0, fun j ↦ Fin.elim0 j, ⟨Iso.refl Z⟩⟩

/-- The additive hull is closed under binary biproducts. -/
instance additiveClosure_isClosedUnderBinaryProducts :
    (show ObjectProperty (ControlFiniteModule k C) from S.additiveClosure).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Z ⟨p⟩
    let X := p.diag.obj ⟨WalkingPair.left⟩
    let Y := p.diag.obj ⟨WalkingPair.right⟩
    obtain ⟨nX, labelX, ⟨eX⟩⟩ := p.prop_diag_obj ⟨WalkingPair.left⟩
    obtain ⟨nY, labelY, ⟨eY⟩⟩ := p.prop_diag_obj ⟨WalkingPair.right⟩
    let dX : CategoryTheory.FiniteIndecomposableDecomposition X :=
      { n := nX
        summand := fun i ↦ S.obj (labelX i)
        indecomposable := fun i ↦ S.indecomposable (labelX i)
        isoBiproduct := eX.symm }
    let dY : CategoryTheory.FiniteIndecomposableDecomposition Y :=
      { n := nY
        summand := fun i ↦ S.obj (labelY i)
        indecomposable := fun i ↦ S.indecomposable (labelY i)
        isoBiproduct := eY.symm }
    let d := dX.biprod dY
    let eZ : X ⊞ Y ≅ Z :=
      biprod.isoProd X Y ≪≫
        Limits.IsLimit.conePointUniqueUpToIso (Limits.prodIsProd X Y)
          ((Limits.IsLimit.postcomposeHomEquiv
            (Limits.diagramIsoPair p.diag) _).2 p.isLimit)
    let label : Fin (nX + nY) → Fin S.n := fun i ↦
      Sum.elim labelX labelY (finSumFinEquiv.symm i)
    have hlabel : (fun i ↦ S.obj (label i)) = d.summand := by
      funext i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · simp [label, d, dX, dY,
          CategoryTheory.FiniteIndecomposableDecomposition.biprod]
      · simp [label, d, dX, dY,
          CategoryTheory.FiniteIndecomposableDecomposition.biprod]
    refine ⟨nX + nY, label, ?_⟩
    exact ⟨biproduct.mapIso (fun i ↦ eqToIso (congrFun hlabel i)) ≪≫
      d.isoBiproduct.symm ≪≫ eZ⟩

/-- Binary biproduct and zero closure give all finite products in the full
subcategory on the additive hull. -/
instance additiveClosure_isClosedUnderFiniteProducts :
    (show ObjectProperty (ControlFiniteModule k C) from S.additiveClosure).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The full subcategory on the additive hull has finite biproducts. -/
instance additiveClosure_hasFiniteBiproducts :
    HasFiniteBiproducts
      (CoveringSeparation.WindowCategory S.additiveClosure) := by
  let P : ObjectProperty (ControlFiniteModule k C) := S.additiveClosure
  letI : P.IsClosedUnderFiniteProducts :=
    S.additiveClosure_isClosedUnderFiniteProducts
  change HasFiniteBiproducts P.FullSubcategory
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- The finite-biproduct structure on the additive hull supplies binary
biproducts explicitly for interfaces which request the two structures
separately. -/
instance additiveClosure_hasBinaryBiproducts :
    HasBinaryBiproducts
      (CoveringSeparation.WindowCategory S.additiveClosure) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- Every object of the additive hull has a displayed decomposition whose
summands remain indecomposable in the ambient finite-module category. -/
theorem exists_finiteIndecomposableDecomposition_additiveClosure
    (X : CoveringSeparation.WindowCategory S.additiveClosure) :
    ∃ d : CategoryTheory.FiniteIndecomposableDecomposition X,
      ∀ i, Indecomposable (d.summand i).1 := by
  letI : HasFiniteBiproducts
      (CoveringSeparation.WindowCategory S.additiveClosure) :=
    S.additiveClosure_hasFiniteBiproducts
  letI : HasBinaryBiproducts
      (CoveringSeparation.WindowCategory S.additiveClosure) :=
    hasBinaryBiproducts_of_finite_biproducts _
  obtain ⟨n, label, ⟨e⟩⟩ := X.2
  let U : Fin n → CoveringSeparation.WindowCategory S.additiveClosure :=
    fun i ↦ ⟨S.obj (label i),
      S.isoClosure_subset_additiveClosure
        (S.obj_mem_isoClosure (label i))⟩
  let J : CoveringSeparation.WindowCategory S.additiveClosure ⥤
      ControlFiniteModule k C :=
    (show ObjectProperty (ControlFiniteModule k C) from
      S.additiveClosure).ι
  letI : J.Additive := by
    change
      (show ObjectProperty (ControlFiniteModule k C) from
        S.additiveClosure).ι.Additive
    exact CategoryTheory.Functor.fullSubcategoryInclusion_additive _
  letI : J.Faithful := by
    change
      (show ObjectProperty (ControlFiniteModule k C) from
        S.additiveClosure).ι.Faithful
    constructor
    intro X Y f g h
    exact InducedCategory.hom_ext h
  let eAmbient : X.1 ≅ J.obj (⨁ U) :=
    e.symm ≪≫ (J.mapBiproduct U).symm
  let eWindow : X ≅ ⨁ U := ObjectProperty.isoMk _ eAmbient
  let d : CategoryTheory.FiniteIndecomposableDecomposition X :=
    { n := n
      summand := U
      indecomposable := fun i ↦
        MagnitudeConjecture.indecomposable_of_faithful_additive
          J (U i) (S.indecomposable (label i))
      isoBiproduct := eWindow }
  exact ⟨d, fun i ↦ S.indecomposable (label i)⟩

/-- A finite representative family together with the fact that it covers the
indecomposable Hom neighbors of every member of the preceding family. -/
structure HomNeighborhoodExtension where
  family : FiniteIndecomposableModuleFamily (k := k) (C := C)
  covers : ∀ i {Y : ControlFiniteModule k C}, Indecomposable Y →
    CoveringSeparation.homInteraction (S.obj i) Y →
      ∃ j, Nonempty (family.obj j ≅ Y)

/-- One symmetric Hom-neighborhood enlargement of a finite representative
family, retaining its coverage certificate. -/
def homNeighborhoodExtension
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    S.HomNeighborhoodExtension := by
  classical
  let H (i : Fin S.n) :=
    finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
      hlocal (S.obj i) (S.indecomposable i)
  let I := Σ i : Fin S.n, Fin (H i).n
  let n := Nat.card I
  let e : Fin n ≃ I := (Finite.equivFin I).symm
  refine
    { family :=
        { n := n
          obj := fun t ↦ (H (e t).1).obj (e t).2
          indecomposable := fun t ↦ (H (e t).1).indecomposable (e t).2 }
      covers := ?_ }
  intro i Y hY hSY
  obtain ⟨j, hj⟩ := (H i).covers hY hSY
  let p : I := ⟨i, j⟩
  refine ⟨e.symm p, ?_⟩
  change Nonempty ((H (e (e.symm p)).1).obj (e (e.symm p)).2 ≅ Y)
  rw [e.apply_symm_apply p]
  exact hj

/-- The finite family underlying one certified Hom-neighborhood extension. -/
abbrev homNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :=
  (S.homNeighborhoodExtension hlocal).family

/-- Every representative in a family Hom-neighborhood shares a support
object with some representative in the preceding family. -/
theorem homNeighborhood_obj_commonSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (t : Fin (S.homNeighborhood hlocal).n) :
    ∃ i : Fin S.n, ∃ X : C,
      X ∈ moduleSupport k (S.obj i).obj.obj ∧
        X ∈ moduleSupport k
          ((S.homNeighborhood hlocal).obj t).obj.obj := by
  classical
  let H (i : Fin S.n) :=
    finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
      hlocal (S.obj i) (S.indecomposable i)
  let I := Σ i : Fin S.n, Fin (H i).n
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  obtain ⟨X, hSX, hHX⟩ :=
    finiteIndecomposableHomNeighborhood_obj_commonSupport
      hlocal (S.obj (e t).1) (S.indecomposable (e t).1) (e t).2
  exact ⟨(e t).1, X, hSX, hHX⟩

/-- Every indecomposable sharing a support object with a representative of a
finite family is represented in the family's Hom-neighborhood. -/
theorem mem_homNeighborhood_isoClosure_of_commonSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {Y : ControlFiniteModule k C} (hY : Indecomposable Y)
    (hcommon : ∃ i : Fin S.n, ∃ X : C,
      X ∈ moduleSupport k (S.obj i).obj.obj ∧
        X ∈ moduleSupport k Y.obj.obj) :
    Y ∈ (S.homNeighborhood hlocal).isoClosure := by
  classical
  let H (i : Fin S.n) :=
    finiteIndecomposableHomNeighborhood_of_locallyRepresentationFinite
      hlocal (S.obj i) (S.indecomposable i)
  let I := Σ i : Fin S.n, Fin (H i).n
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  obtain ⟨i, X, hSX, hYX⟩ := hcommon
  obtain ⟨j, hj⟩ := finiteIndecomposableHomNeighborhood_covers_commonSupport
    hlocal (S.obj i) (S.indecomposable i) hY ⟨X, hSX, hYX⟩
  let p : I := ⟨i, j⟩
  refine ⟨e.symm p, ?_⟩
  change Nonempty ((H (e (e.symm p)).1).obj (e (e.symm p)).2 ≅ Y)
  rw [e.apply_symm_apply p]
  exact hj

/-- The isomorphism closure of the enlarged family contains the full
set-valued Hom-interaction neighborhood of the previous closure. -/
theorem interactionNeighborhood_isoClosure_subset_homNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    CoveringSeparation.interactionNeighborhood
        indecomposableHomInteraction S.isoClosure ⊆
      (S.homNeighborhood hlocal).isoClosure := by
  classical
  intro Y hY
  obtain ⟨X, ⟨i, ⟨eX⟩⟩, hYind, hXY⟩ := hY
  have hSY : CoveringSeparation.homInteraction (S.obj i) Y := by
    rcases hXY with hEq | hforward | hbackward
    · subst Y
      have he : eX.hom ≠ 0 := by
        intro hezero
        apply (S.indecomposable i).1
        rw [Limits.IsZero.iff_id_eq_zero]
        calc
          𝟙 (S.obj i) = eX.hom ≫ eX.inv := by simp
          _ = 0 := by simp [hezero]
      exact Or.inr (Or.inl ⟨⟨eX.hom, 0, he⟩⟩)
    · exact Or.inr (Or.inl
        ((Iso.homCongr eX.symm (Iso.refl Y)).nontrivial_congr.mp hforward))
    · exact Or.inr (Or.inr
        ((Iso.homCongr (Iso.refl Y) eX.symm).nontrivial_congr.mp hbackward))
  exact (S.homNeighborhoodExtension hlocal).covers i hYind hSY

/-- Iterated finite representative families for successive symmetric Hom
neighborhoods. -/
def iterateHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    ℕ → FiniteIndecomposableModuleFamily (k := k) (C := C)
  | 0 => S
  | n + 1 => homNeighborhood (iterateHomNeighborhood hlocal n) hlocal

/-- Each iterated isomorphism-saturated window contains the full Hom
neighborhood of the preceding one. -/
theorem interactionNeighborhood_iterateHomNeighborhood_subset
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (n : ℕ) :
    CoveringSeparation.interactionNeighborhood
        indecomposableHomInteraction
        (S.iterateHomNeighborhood hlocal n).isoClosure ⊆
      (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure := by
  simpa only [iterateHomNeighborhood] using
    (S.iterateHomNeighborhood hlocal n).interactionNeighborhood_isoClosure_subset_homNeighborhood
      hlocal

/-- An indecomposable interacting with a member of the `n`th certified Hom
neighborhood belongs to the next neighborhood. -/
theorem mem_iterateHomNeighborhood_succ_of_homInteraction
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {n : ℕ} {X Y : ControlFiniteModule k C}
    (hX : X ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (hY : Indecomposable Y)
    (hXY : CoveringSeparation.homInteraction X Y) :
    Y ∈ (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure :=
  S.interactionNeighborhood_iterateHomNeighborhood_subset hlocal n
    ⟨X, hX, hY, hXY⟩

/-- A nonzero map out of a member of the `n`th neighborhood puts its
indecomposable target in the next neighborhood. -/
theorem mem_iterateHomNeighborhood_succ_of_ne_zero_to
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {n : ℕ} {X Y : ControlFiniteModule k C}
    (hX : X ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (hY : Indecomposable Y) (f : X ⟶ Y) (hf : f ≠ 0) :
    Y ∈ (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure :=
  S.mem_iterateHomNeighborhood_succ_of_homInteraction hlocal hX hY
    (Or.inr (Or.inl ⟨⟨f, 0, hf⟩⟩))

/-- A nonzero map into a member of the `n`th neighborhood puts its
indecomposable source in the next neighborhood. -/
theorem mem_iterateHomNeighborhood_succ_of_ne_zero_from
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {n : ℕ} {X Y : ControlFiniteModule k C}
    (hX : X ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (hY : Indecomposable Y) (f : Y ⟶ X) (hf : f ≠ 0) :
    Y ∈ (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure :=
  S.mem_iterateHomNeighborhood_succ_of_homInteraction hlocal hX hY
    (Or.inr (Or.inr ⟨⟨f, 0, hf⟩⟩))

/-- An indecomposable nonzero factorization witness whose source endpoint is
in the `n`th neighborhood belongs to the next neighborhood and interacts
with both endpoints. -/
theorem bifactor_mem_iterateHomNeighborhood_succ
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {n : ℕ} {X Y Z : ControlFiniteModule k C}
    (hX : X ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (hZ : Indecomposable Z) (a : X ⟶ Z) (ha : a ≠ 0)
    (b : Z ⟶ Y) (hb : b ≠ 0) :
    Z ∈ (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure ∧
      CoveringSeparation.homInteraction X Z ∧
      CoveringSeparation.homInteraction Y Z := by
  let hXZ : CoveringSeparation.homInteraction X Z :=
    Or.inr (Or.inl ⟨⟨a, 0, ha⟩⟩)
  let hYZ : CoveringSeparation.homInteraction Y Z :=
    Or.inr (Or.inr ⟨⟨b, 0, hb⟩⟩)
  exact ⟨S.mem_iterateHomNeighborhood_succ_of_homInteraction
      hlocal hX hZ hXZ, hXZ, hYZ⟩

/-- The manuscript's three-step finite control family. -/
abbrev threeStepControlFamily
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :=
  S.iterateHomNeighborhood hlocal 3

/-- The manuscript's `U₃` clause: an indecomposable through which a morphism
out of a `U₂` term factors with both factors nonzero belongs to the
three-step control family.  In the application the target is a `U₂` term as
well. -/
theorem bifactor_mem_threeStepControlFamily
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {X Y Z : ControlFiniteModule k C}
    (hX : X ∈ (S.iterateHomNeighborhood hlocal 2).isoClosure)
    (hZ : Indecomposable Z) (a : X ⟶ Z) (ha : a ≠ 0)
    (b : Z ⟶ Y) (hb : b ≠ 0) :
    Z ∈ (S.threeStepControlFamily hlocal).isoClosure :=
  (S.bifactor_mem_iterateHomNeighborhood_succ
    hlocal hX hZ a ha b hb).1

end FiniteIndecomposableModuleFamily

/-- The finite seed family representing the manuscript's set `H_x` of
indecomposables nonzero at the base object `x`. -/
def finiteFiberControlSeed
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (X : C) :
    FiniteIndecomposableModuleFamily (k := k) (C := C) := by
  classical
  let H := Classical.choice (hlocal X)
  let I := Finset.univ.filter fun j : Fin H.n ↦
    Nontrivial ((H.obj j).obj.obj.obj X)
  exact H.toModuleFamily.subfamily I

/-- Every representative retained in the fibre seed is genuinely nonzero at
the base object.  This exactness prevents an overcomplete local-finiteness
witness from changing a local-density sum. -/
theorem finiteFiberControlSeed_obj_nontrivial
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (X : C)
    (i : Fin (finiteFiberControlSeed hlocal X).n) :
    Nontrivial (((finiteFiberControlSeed hlocal X).obj i).obj.obj.obj X) := by
  classical
  let H := Classical.choice (hlocal X)
  let I := Finset.univ.filter fun j : Fin H.n ↦
    Nontrivial ((H.obj j).obj.obj.obj X)
  change Nontrivial
    ((H.obj ((I.equivFin.symm i).1)).obj.obj.obj X)
  exact (Finset.mem_filter.mp (I.equivFin.symm i).property).2

/-- Every indecomposable finite module nonzero at `x` belongs to the
isomorphism-saturated seed window represented by `finiteFiberControlSeed`. -/
theorem mem_finiteFiberControlSeed_isoClosure
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (X : C)
    {M : ControlFiniteModule k C} (hM : Indecomposable M)
    (hMX : Nontrivial (M.obj.obj.obj X)) :
    M ∈ (finiteFiberControlSeed hlocal X).isoClosure := by
  classical
  let H := Classical.choice (hlocal X)
  let I := Finset.univ.filter fun j : Fin H.n ↦
    Nontrivial ((H.obj j).obj.obj.obj X)
  obtain ⟨j, ⟨e⟩⟩ := H.covers hM hMX
  have hjX : Nontrivial ((H.obj j).obj.obj.obj X) := by
    let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    let eX := (J.mapIso
      ((IsFiniteDimensionalModule (C := C) k).ι.mapIso e)).app X
    exact eX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hMX
  have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjX⟩
  let js : I := ⟨j, hjI⟩
  refine ⟨I.equivFin js, ?_⟩
  change Nonempty (H.obj (I.equivFin.symm (I.equivFin js)).1 ≅ M)
  rw [I.equivFin.symm_apply_apply]
  exact ⟨e⟩

/-- The manuscript's three successive indecomposable Hom neighborhoods of
`H_x`, represented by one finite family. -/
abbrev finiteThreeStepControlFamily
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (X : C) :=
  (finiteFiberControlSeed hlocal X).threeStepControlFamily hlocal

end MagnitudeConjecture.CoveringHom
