import MagnitudeConjecture.Algebra.RightModulePrimitiveArrowGain
import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundary
import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian

/-!
# Crossing arrows and ambient meshes for primitive deletion

This file formalizes the crossing-mesh lemma in the live manuscript.  Its
first layer records the exact primitive-coordinate equation on every ambient
Auslander--Reiten sequence and the quotient/submodule closure which prevents
a crossing arrow from starting at an injective killed object or ending at a
projective killed object.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : RightModule.PrimitiveIdempotentData e)

/-- Applying the primitive projective coordinate to an ambient
Auslander--Reiten sequence gives the manuscript's additive equation
`d_(tau z) + d_z = sum_y a(y,z)d_y`, with displayed arrow occurrences on
the right. -/
theorem sum_primitiveMultiplicity_minimalRightMiddle_eq
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    (∑ i : (S.minimalRightAlmostSplitAt z.1).index,
        S.primitiveMultiplicity D
          ((S.minimalRightAlmostSplitAt z.1).label i)) =
      S.primitiveMultiplicity D (S.rightTranslationLabel z) +
        S.primitiveMultiplicity D z.1 := by
  classical
  let B := S.minimalRightAlmostSplitAt z.1
  let p := S.primitiveSourceProjectiveLabel D
  have hmiddle := congrFun
    (S.projectiveHomVectorFGObj_middle_eq_add
      (S.ambientARShortComplex_shortExact z)) p
  have hdecomposition :
      Module.finrank k (S.fgObj p.label ⟶ B.middle) =
        ∑ i : B.index,
          Module.finrank k (S.fgObj p.label ⟶ S.fgObj (B.label i)) := by
    exact
      MagnitudeConjecture.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
        k (S.fgObj p.label) B.middle
          (fun i : B.index ↦ S.fgObj (B.label i)) B.decomposition
  change
    (Module.finrank k (S.fgObj p.label ⟶ B.middle) : ℤ) =
      (Module.finrank k
        (S.fgObj p.label ⟶ S.fgObj (S.rightTranslationLabel z)) : ℤ) +
      Module.finrank k (S.fgObj p.label ⟶ S.fgObj z.1) at hmiddle
  rw [hdecomposition] at hmiddle
  simp_rw [show ∀ x : Fin S.n,
      Module.finrank k (S.fgObj p.label ⟶ S.fgObj x) =
        S.primitiveMultiplicity D x by
    intro x
    exact (S.primitiveMultiplicity_eq_sourceHom D x).symm] at hmiddle
  exact_mod_cast hmiddle

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- The `AeA`-annihilated labels are closed under epimorphic images. -/
theorem mem_primitiveKilledLabels_of_epi
    {x y : Fin S.n}
    (hx : x ∈ S.primitiveKilledLabels D)
    (f : S.fgObj x ⟶ S.fgObj y) [Epi f] :
    y ∈ S.primitiveKilledLabels D := by
  intro m
  obtain ⟨a, rfl⟩ :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance m
  change (MulOpposite.op e) • f.hom.hom a = 0
  calc
    (MulOpposite.op e) • f.hom.hom a =
        f.hom.hom ((MulOpposite.op e) • a) :=
      (f.hom.hom.map_smul (MulOpposite.op e) a).symm
    _ = f.hom.hom 0 := congrArg f.hom.hom (hx a)
    _ = 0 := f.hom.hom.map_zero

omit [FiniteDimensional k A] in
/-- The `AeA`-annihilated labels are closed under subobjects. -/
theorem mem_primitiveKilledLabels_of_mono
    {x y : Fin S.n}
    (hy : y ∈ S.primitiveKilledLabels D)
    (f : S.fgObj x ⟶ S.fgObj y) [Mono f] :
    x ∈ S.primitiveKilledLabels D := by
  intro m
  apply (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
  change f.hom.hom ((MulOpposite.op e) • m) = f.hom.hom 0
  rw [f.hom.hom.map_smul, hy (f.hom.hom m), map_zero]

omit [FiniteDimensional k A] in
/-- An irreducible arrow leaving the killed subcategory cannot start at an
injective ambient module. -/
theorem not_injective_of_irreducible_from_primitiveKilled
    {x y : Fin S.n}
    (hx : x ∈ S.primitiveKilledLabels D)
    (hy : y ∉ S.primitiveKilledLabels D)
    (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) :
    ¬ Injective (S.fgObj x) := by
  intro hxInjective
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    letI : Injective (S.fgObj x) := hxInjective
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 (S.fgObj x)) f
        id := Injective.comp_factorThru (𝟙 (S.fgObj x)) f }
  · letI : Epi f := hepi
    exact hy (S.mem_primitiveKilledLabels_of_epi D hx f)

omit [FiniteDimensional k A] in
/-- An irreducible arrow entering the killed subcategory cannot end at a
projective ambient module. -/
theorem not_projective_of_irreducible_to_primitiveKilled
    {x y : Fin S.n}
    (hx : x ∉ S.primitiveKilledLabels D)
    (hy : y ∈ S.primitiveKilledLabels D)
    (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) :
    ¬ Projective (S.fgObj y) := by
  intro hyProjective
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    exact hx (S.mem_primitiveKilledLabels_of_mono D hy f)
  · letI : Epi f := hepi
    letI : Projective (S.fgObj y) := hyProjective
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := Projective.factorThru (𝟙 (S.fgObj y)) f
        id := Projective.factorThru_comp (𝟙 (S.fgObj y)) f }

/-- If an incoming mesh occurrence crosses from the non-killed side into a
killed endpoint, then the ambient translate of that endpoint is non-killed.
This is the first orientation of the manuscript's crossing-sum argument. -/
theorem rightTranslation_not_mem_of_meshArrow_to_primitiveKilled
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)})
    (y : Fin S.n)
    (hz : z.1 ∈ S.primitiveKilledLabels D)
    (hy : y ∉ S.primitiveKilledLabels D)
    (a : S.MeshArrow z.1 y) :
    S.rightTranslationLabel z ∉ S.primitiveKilledLabels D := by
  classical
  let B := S.minimalRightAlmostSplitAt z.1
  let a' : S.almostSplitSkeleton.RightAROccurrence B y := by
    change S.almostSplitSkeleton.RightAROccurrence
      (S.meshRightAlmostSplitAt z.1) y at a
    rw [S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2] at a
    exact a
  have hypos : 0 < S.primitiveMultiplicity D y := by
    exact PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) (S.primitiveMultiplicityInput D)
        (⟨y, hy⟩ : S.SurvivingLabel (S.primitiveKilledLabels D))
  have hterm : 0 < S.primitiveMultiplicity D (B.label a'.1) := by
    simpa only [a'.2] using hypos
  have hle :
      S.primitiveMultiplicity D (B.label a'.1) ≤
        ∑ i : B.index, S.primitiveMultiplicity D (B.label i) := by
    exact Finset.single_le_sum
      (fun i _hi ↦ Nat.zero_le (S.primitiveMultiplicity D (B.label i)))
      (Finset.mem_univ a'.1)
  have hsumpos :
      0 < ∑ i : B.index, S.primitiveMultiplicity D (B.label i) :=
    lt_of_lt_of_le hterm hle
  have hsum := S.sum_primitiveMultiplicity_minimalRightMiddle_eq D z
  have hzzero : S.primitiveMultiplicity D z.1 = 0 :=
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D z.1).1 hz
  rw [hsum, hzzero, Nat.add_zero] at hsumpos
  intro htranslation
  have hzero :
      S.primitiveMultiplicity D (S.rightTranslationLabel z) = 0 :=
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D _).1
      htranslation
  omega

/-- If a mesh occurrence crosses out of a killed source, the inverse
ambient translate of that source is non-killed.  Pairing the two sides of an
ambient mesh reduces this to the preceding crossing-sum orientation. -/
theorem inverseTranslation_not_mem_of_meshArrow_from_primitiveKilled
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)})
    (y : Fin S.n)
    (hx : x.1 ∈ S.primitiveKilledLabels D)
    (hy : y ∉ S.primitiveKilledLabels D)
    (a : S.MeshArrow y x.1) :
    ((S.rightTranslationEquiv).symm x).1 ∉
      S.primitiveKilledLabels D := by
  let z := (S.rightTranslationEquiv).symm x
  have htranslate : S.rightTranslationLabel z = x.1 :=
    congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply x)
  let a' : S.MeshArrow y (S.rightTranslationLabel z) := by
    simpa only [htranslate] using a
  let b : S.MeshArrow z.1 y := (S.meshArrowEquiv H z y).symm a'
  intro hz
  have hnot :=
    S.rightTranslation_not_mem_of_meshArrow_to_primitiveKilled
      D z y hz hy b
  exact hnot (by simpa only [htranslate] using hx)

/-- Ambient arrow occurrences entering the primitive-quotient subcategory.
The stored mesh arrow represents the irreducible map `source ⟶ target`. -/
abbrev PrimitiveIncomingCrossingArrow :=
  {a : Σ target : Fin S.n, Σ source : Fin S.n,
      S.MeshArrow target source //
    a.1 ∈ S.primitiveKilledLabels D ∧
      a.2.1 ∉ S.primitiveKilledLabels D}

/-- Ambient arrow occurrences leaving the primitive-quotient subcategory. -/
abbrev PrimitiveOutgoingCrossingArrow :=
  {a : Σ target : Fin S.n, Σ source : Fin S.n,
      S.MeshArrow target source //
    a.1 ∉ S.primitiveKilledLabels D ∧
      a.2.1 ∈ S.primitiveKilledLabels D}

/-- All ambient arrows crossing between the quotient labels and their
complement, with parallel occurrences retained. -/
abbrev PrimitiveCrossingArrow :=
  S.PrimitiveIncomingCrossingArrow D ⊕
    S.PrimitiveOutgoingCrossingArrow D

/-- Ambient meshes whose right endpoint is killed while its translate is
not killed. -/
abbrev PrimitiveIncomingBoundaryMesh :=
  {z : {x : Fin S.n // ¬ Projective (S.fgObj x)} //
    z.1 ∈ S.primitiveKilledLabels D ∧
      S.rightTranslationLabel z ∉ S.primitiveKilledLabels D}

/-- Ambient meshes whose right endpoint is not killed while its translate
is killed. -/
abbrev PrimitiveOutgoingBoundaryMesh :=
  {z : {x : Fin S.n // ¬ Projective (S.fgObj x)} //
    z.1 ∉ S.primitiveKilledLabels D ∧
      S.rightTranslationLabel z ∈ S.primitiveKilledLabels D}

/-- Ambient meshes with translation endpoints on opposite sides of the
primitive deletion. -/
abbrev PrimitiveBoundaryMesh :=
  S.PrimitiveIncomingBoundaryMesh D ⊕
    S.PrimitiveOutgoingBoundaryMesh D

/-- Forget the orientation tag of a boundary mesh. -/
def primitiveBoundaryMeshEndpoint
    (z : S.PrimitiveBoundaryMesh D) :
    {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
  Sum.elim Subtype.val Subtype.val z

/-- A crossing arrow entering the killed subcategory determines the ambient
mesh ending at its target. -/
def incomingCrossingArrowBoundaryMesh
    (a : S.PrimitiveIncomingCrossingArrow D) :
    S.PrimitiveIncomingBoundaryMesh D := by
  let target := a.1.1
  let source := a.1.2.1
  let arrow := a.1.2.2
  have htarget : target ∈ S.primitiveKilledLabels D := a.2.1
  have hsource : source ∉ S.primitiveKilledLabels D := a.2.2
  have hnp : ¬ Projective (S.fgObj target) :=
    S.not_projective_of_irreducible_to_primitiveKilled D
      hsource htarget (S.meshArrowMap arrow)
        (S.meshArrowMap_isIrreducible arrow)
  let z : {x : Fin S.n // ¬ Projective (S.fgObj x)} := ⟨target, hnp⟩
  exact ⟨z, htarget,
    S.rightTranslation_not_mem_of_meshArrow_to_primitiveKilled
      D z source htarget hsource arrow⟩

/-- A crossing arrow leaving the killed subcategory determines the ambient
mesh whose left translation endpoint is its source. -/
def outgoingCrossingArrowBoundaryMesh
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a : S.PrimitiveOutgoingCrossingArrow D) :
    S.PrimitiveOutgoingBoundaryMesh D := by
  let target := a.1.1
  let source := a.1.2.1
  let arrow := a.1.2.2
  have htarget : target ∉ S.primitiveKilledLabels D := a.2.1
  have hsource : source ∈ S.primitiveKilledLabels D := a.2.2
  have hni : ¬ Injective (S.fgObj source) :=
    S.not_injective_of_irreducible_from_primitiveKilled D
      hsource htarget (S.meshArrowMap arrow)
        (S.meshArrowMap_isIrreducible arrow)
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} := ⟨source, hni⟩
  let z := (S.rightTranslationEquiv).symm x
  have htranslate : S.rightTranslationLabel z = source :=
    congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply x)
  have hz : z.1 ∉ S.primitiveKilledLabels D :=
    S.inverseTranslation_not_mem_of_meshArrow_from_primitiveKilled
      D H x target hsource htarget arrow
  exact ⟨z, hz, by simpa only [htranslate] using hsource⟩

/-- The manuscript's map from crossing arrows to meshes with opposite
translation endpoints. -/
def crossingArrowBoundaryMesh
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.PrimitiveCrossingArrow D → S.PrimitiveBoundaryMesh D
  | Sum.inl a => Sum.inl (S.incomingCrossingArrowBoundaryMesh D a)
  | Sum.inr a => Sum.inr (S.outgoingCrossingArrowBoundaryMesh D H a)

/-- Displayed middle occurrences lying on the non-killed side of an ambient
mesh. -/
abbrev PrimitiveNonKilledMiddleOccurrence
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :=
  {a : Σ y : Fin S.n, S.MeshArrow z.1 y //
    a.1 ∉ S.primitiveKilledLabels D}

/-- The displayed-index and labelled-arrow descriptions of a surviving
middle occurrence are equivalent, with parallel occurrences retained. -/
def primitiveNonKilledMiddleIndexEquiv
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    {i : (S.meshRightAlmostSplitAt z.1).index //
      (S.meshRightAlmostSplitAt z.1).label i ∉
        S.primitiveKilledLabels D} ≃
      S.PrimitiveNonKilledMiddleOccurrence D z where
  toFun i :=
    ⟨⟨(S.meshRightAlmostSplitAt z.1).label i.1, ⟨i.1, rfl⟩⟩,
      i.2⟩
  invFun a := ⟨a.1.2.1, by simpa only [a.1.2.2] using a.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨y, ⟨i, hi⟩⟩, hy⟩
    subst y
    rfl

/-- Incoming crossing arrows are the surviving middle occurrences in the
boundary meshes ending on the killed side. -/
def incomingCrossingArrowEquivBoundaryOccurrence :
    S.PrimitiveIncomingCrossingArrow D ≃
      Σ z : S.PrimitiveIncomingBoundaryMesh D,
        S.PrimitiveNonKilledMiddleOccurrence D z.1 := by
  classical
  refine
    { toFun := fun a ↦ ?_
      invFun := fun zi ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · let z := S.incomingCrossingArrowBoundaryMesh D a
    let arrow : S.MeshArrow z.1.1 a.1.2.1 := by
      simpa only [z, incomingCrossingArrowBoundaryMesh] using a.1.2.2
    exact ⟨z, ⟨⟨a.1.2.1, arrow⟩, a.2.2⟩⟩
  · let z := zi.1
    let a := zi.2
    exact ⟨⟨z.1.1, a.1.1, a.1.2⟩, z.2.1, a.2⟩
  · rintro ⟨⟨target, source, arrow⟩, htarget, hsource⟩
    rfl
  · rintro ⟨⟨⟨target, htargetProjective⟩, htarget, htranslation⟩,
      ⟨⟨source, arrow⟩, hsource⟩⟩
    rfl

/-- Pair an outgoing crossing arrow across its ambient mesh and retain its
middle occurrence on the non-killed side. -/
def outgoingCrossingArrowBoundaryOccurrence
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a : S.PrimitiveOutgoingCrossingArrow D) :
      Σ z : S.PrimitiveOutgoingBoundaryMesh D,
        S.PrimitiveNonKilledMiddleOccurrence D z.1 := by
  classical
  let z := S.outgoingCrossingArrowBoundaryMesh D H a
  have htranslate : S.rightTranslationLabel z.1 = a.1.2.1 := by
    dsimp only [z, outgoingCrossingArrowBoundaryMesh]
    exact congrArg Subtype.val
      (S.rightTranslationEquiv.apply_symm_apply _)
  let pairedArrow :
      S.MeshArrow a.1.1 (S.rightTranslationLabel z.1) := by
    rw [htranslate]
    exact a.1.2.2
  let arrow : S.MeshArrow z.1.1 a.1.1 :=
    (S.meshArrowEquiv H z.1 a.1.1).symm pairedArrow
  exact ⟨z, ⟨⟨a.1.1, arrow⟩, a.2.1⟩⟩

/-- Reconstruct an outgoing crossing arrow from its paired middle
occurrence. -/
def outgoingBoundaryOccurrenceCrossingArrow
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (zi : Σ z : S.PrimitiveOutgoingBoundaryMesh D,
      S.PrimitiveNonKilledMiddleOccurrence D z.1) :
    S.PrimitiveOutgoingCrossingArrow D := by
  classical
  let z := zi.1
  let a := zi.2
  let y := a.1.1
  let arrow : S.MeshArrow z.1.1 y := a.1.2
  let pairedArrow : S.MeshArrow y (S.rightTranslationLabel z.1) :=
    S.meshArrowEquiv H z.1 y arrow
  exact ⟨⟨y, S.rightTranslationLabel z.1, pairedArrow⟩, a.2, z.2.2⟩

private theorem outgoingBoundaryMesh_recovered
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (zi : Σ z : S.PrimitiveOutgoingBoundaryMesh D,
      S.PrimitiveNonKilledMiddleOccurrence D z.1) :
    S.outgoingCrossingArrowBoundaryMesh D H
        (S.outgoingBoundaryOccurrenceCrossingArrow D H zi) = zi.1 := by
  apply Subtype.ext
  change
    (S.rightTranslationEquiv).symm
        ⟨S.rightTranslationLabel zi.1.1,
          (S.rightTranslationEquiv zi.1.1).2⟩ = zi.1.1
  have hx :
      (⟨S.rightTranslationLabel zi.1.1,
          (S.rightTranslationEquiv zi.1.1).2⟩ :
          {x : Fin S.n // ¬ Injective (S.fgObj x)}) =
        S.rightTranslationEquiv zi.1.1 := by
    apply Subtype.ext
    rfl
  rw [hx]
  exact S.rightTranslationEquiv.symm_apply_apply zi.1.1

private theorem card_eq_one_of_sum_eq_one_of_pos
    {I : Type u} [Fintype I]
    (weight : I → ℕ)
    (hpositive : ∀ i, 0 < weight i)
    (hsum : ∑ i, weight i = 1) :
    Fintype.card I = 1 := by
  classical
  have hle : ∑ _i : I, 1 ≤ ∑ i : I, weight i := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hpositive i
  have hcardle : Fintype.card I ≤ 1 := by
    calc
      Fintype.card I = ∑ _i : I, 1 := by simp
      _ ≤ ∑ i : I, weight i := hle
      _ = 1 := hsum
  have hcardne : Fintype.card I ≠ 0 := by
    intro hzero
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp hzero
    simp at hsum
  omega

/-- At a boundary mesh ending on the killed side, the full displayed
primitive-coordinate sum is one. -/
theorem sum_primitiveMultiplicity_incomingBoundaryMesh_eq_one
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (z : S.PrimitiveIncomingBoundaryMesh D) :
    (∑ i : (S.minimalRightAlmostSplitAt z.1.1).index,
        S.primitiveMultiplicity D
          ((S.minimalRightAlmostSplitAt z.1.1).label i)) = 1 := by
  have hsum := S.sum_primitiveMultiplicity_minimalRightMiddle_eq D z.1
  have hzZero : S.primitiveMultiplicity D z.1.1 = 0 :=
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D _).1
      z.2.1
  have htauPos : 0 <
      S.primitiveMultiplicity D (S.rightTranslationLabel z.1) :=
    PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) (S.primitiveMultiplicityInput D)
        (⟨S.rightTranslationLabel z.1, z.2.2⟩ :
          S.SurvivingLabel (S.primitiveKilledLabels D))
  have hdiff := E.translation_difference_le_one z.1
  have htauLeInt :
      (S.primitiveMultiplicity D (S.rightTranslationLabel z.1) : ℤ) ≤ 1 := by
    have hneg := le_trans
      (neg_le_abs ((S.primitiveMultiplicity D z.1.1 : ℤ) -
        S.primitiveMultiplicity D (S.rightTranslationLabel z.1))) hdiff
    simpa only [hzZero, Nat.cast_zero, zero_sub, neg_neg] using hneg
  have htauLe :
      S.primitiveMultiplicity D (S.rightTranslationLabel z.1) ≤ 1 := by
    exact_mod_cast htauLeInt
  have htau :
      S.primitiveMultiplicity D (S.rightTranslationLabel z.1) = 1 := by
    omega
  simpa only [hzZero, htau, Nat.add_zero] using hsum

/-- At a boundary mesh ending on the non-killed side, the full displayed
primitive-coordinate sum is also one. -/
theorem sum_primitiveMultiplicity_outgoingBoundaryMesh_eq_one
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (z : S.PrimitiveOutgoingBoundaryMesh D) :
    (∑ i : (S.minimalRightAlmostSplitAt z.1.1).index,
        S.primitiveMultiplicity D
          ((S.minimalRightAlmostSplitAt z.1.1).label i)) = 1 := by
  have hsum := S.sum_primitiveMultiplicity_minimalRightMiddle_eq D z.1
  have htauZero :
      S.primitiveMultiplicity D (S.rightTranslationLabel z.1) = 0 :=
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D _).1
      z.2.2
  have hzPos : 0 < S.primitiveMultiplicity D z.1.1 :=
    PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) (S.primitiveMultiplicityInput D)
        (⟨z.1.1, z.2.1⟩ :
          S.SurvivingLabel (S.primitiveKilledLabels D))
  have hdiff := E.translation_difference_le_one z.1
  have hzLeInt : (S.primitiveMultiplicity D z.1.1 : ℤ) ≤ 1 := by
    have hpos := le_trans
      (le_abs_self ((S.primitiveMultiplicity D z.1.1 : ℤ) -
        S.primitiveMultiplicity D (S.rightTranslationLabel z.1))) hdiff
    simpa only [htauZero, Nat.cast_zero, sub_zero] using hpos
  have hzLe : S.primitiveMultiplicity D z.1.1 ≤ 1 := by
    exact_mod_cast hzLeInt
  have hzOne : S.primitiveMultiplicity D z.1.1 = 1 := by omega
  simpa only [htauZero, hzOne, zero_add] using hsum

private theorem card_primitiveNonKilledMiddleOccurrence_eq_one_of_sum_eq_one
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)})
    (hsum :
      (∑ i : (S.minimalRightAlmostSplitAt z.1).index,
          S.primitiveMultiplicity D
            ((S.minimalRightAlmostSplitAt z.1).label i)) = 1) :
    Nat.card (S.PrimitiveNonKilledMiddleOccurrence D z) = 1 := by
  classical
  let B := S.minimalRightAlmostSplitAt z.1
  let survives : B.index → Prop := fun i ↦
    B.label i ∉ S.primitiveKilledLabels D
  let I := {i : B.index // survives i}
  letI : DecidablePred survives := Classical.decPred survives
  have hI : Nat.card I = 1 := by
    letI : Fintype I := Subtype.fintype survives
    have hkilled :
        (∑ i : {i : B.index // ¬ survives i},
          S.primitiveMultiplicity D (B.label i.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      apply (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero
        D (B.label i.1)).1
      exact not_not.mp i.2
    have hpartition := Fintype.sum_subtype_add_sum_subtype survives
      (fun i : B.index ↦ S.primitiveMultiplicity D (B.label i))
    rw [hkilled, add_zero] at hpartition
    have hsurvives :
        (∑ i : I, S.primitiveMultiplicity D (B.label i.1)) = 1 := by
      calc
        (∑ i : I, S.primitiveMultiplicity D (B.label i.1)) =
            ∑ i : B.index, S.primitiveMultiplicity D (B.label i) := by
          simpa only [I] using hpartition
        _ = 1 := by simpa only [B] using hsum
    rw [Nat.card_eq_fintype_card]
    apply card_eq_one_of_sum_eq_one_of_pos
      (fun i : I ↦ S.primitiveMultiplicity D (B.label i.1))
    · intro i
      exact PrimitiveMultiplicityInput.multiplicity_pos
        (S := S) (S.primitiveMultiplicityInput D)
          (⟨B.label i.1, i.2⟩ :
            S.SurvivingLabel (S.primitiveKilledLabels D))
    · exact hsurvives
  calc
    Nat.card (S.PrimitiveNonKilledMiddleOccurrence D z) =
        Nat.card
          {i : (S.meshRightAlmostSplitAt z.1).index //
            (S.meshRightAlmostSplitAt z.1).label i ∉
              S.primitiveKilledLabels D} :=
      Nat.card_congr (S.primitiveNonKilledMiddleIndexEquiv D z).symm
    _ = Nat.card
          {i : (S.minimalRightAlmostSplitAt z.1).index //
            (S.minimalRightAlmostSplitAt z.1).label i ∉
              S.primitiveKilledLabels D} := by
      rw [S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2]
    _ = 1 := by simpa only [I, survives, B] using hI

/-- Every ambient boundary mesh has exactly one displayed middle occurrence
on the non-killed side. -/
theorem card_primitiveNonKilledMiddleOccurrence_eq_one
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D))
    (z : S.PrimitiveBoundaryMesh D) :
    Nat.card (S.PrimitiveNonKilledMiddleOccurrence D
      (S.primitiveBoundaryMeshEndpoint D z)) = 1 := by
  rcases z with z | z
  · exact S.card_primitiveNonKilledMiddleOccurrence_eq_one_of_sum_eq_one
      D z.1 (S.sum_primitiveMultiplicity_incomingBoundaryMesh_eq_one D E z)
  · exact S.card_primitiveNonKilledMiddleOccurrence_eq_one_of_sum_eq_one
      D z.1 (S.sum_primitiveMultiplicity_outgoingBoundaryMesh_eq_one D E z)

/-- Outgoing crossing arrows, paired across their ambient mesh, are the
surviving middle occurrences in the boundary meshes ending on the
non-killed side.  Uniqueness of the surviving occurrence makes the result
independent of the proof transports used to recover the inverse translate. -/
def outgoingCrossingArrowEquivBoundaryOccurrence
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D)) :
    S.PrimitiveOutgoingCrossingArrow D ≃
      Σ z : S.PrimitiveOutgoingBoundaryMesh D,
        S.PrimitiveNonKilledMiddleOccurrence D z.1 where
  toFun := S.outgoingCrossingArrowBoundaryOccurrence D H
  invFun := S.outgoingBoundaryOccurrenceCrossingArrow D H
  left_inv := by
    intro a
    let z := S.outgoingCrossingArrowBoundaryMesh D H a
    have htranslate : S.rightTranslationLabel z.1 = a.1.2.1 := by
      dsimp only [z, outgoingCrossingArrowBoundaryMesh]
      exact congrArg Subtype.val
        (S.rightTranslationEquiv.apply_symm_apply _)
    let pairedArrow :
        S.MeshArrow a.1.1 (S.rightTranslationLabel z.1) := by
      rw [htranslate]
      exact a.1.2.2
    let arrow : S.MeshArrow z.1.1 a.1.1 :=
      (S.meshArrowEquiv H z.1 a.1.1).symm pairedArrow
    change S.outgoingBoundaryOccurrenceCrossingArrow D H
      ⟨z, ⟨⟨a.1.1, arrow⟩, _⟩⟩ = a
    apply Subtype.ext
    dsimp only [outgoingBoundaryOccurrenceCrossingArrow]
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Sigma.ext htranslate
    simp only [arrow, pairedArrow, Equiv.apply_symm_apply]
    exact cast_heq _ _
  right_inv := by
    rintro ⟨z, i⟩
    let zi : Σ z : S.PrimitiveOutgoingBoundaryMesh D,
        S.PrimitiveNonKilledMiddleOccurrence D z.1 := ⟨z, i⟩
    have hz := S.outgoingBoundaryMesh_recovered D H zi
    apply Sigma.ext hz
    apply heq_of_cast_eq
      (congrArg (fun w : S.PrimitiveOutgoingBoundaryMesh D ↦
        S.PrimitiveNonKilledMiddleOccurrence D w.1) hz)
    have hcard :
        Nat.card (S.PrimitiveNonKilledMiddleOccurrence D z.1) = 1 := by
      have h :=
        S.card_primitiveNonKilledMiddleOccurrence_eq_one D E (Sum.inr z)
      change Nat.card
        (S.PrimitiveNonKilledMiddleOccurrence D z.1) = 1 at h
      exact h
    exact (Nat.card_eq_one_iff_unique.mp hcard).1.elim _ _

/-- Both crossing orientations together are the disjoint union, over
boundary meshes, of their surviving middle occurrences. -/
def crossingArrowEquivBoundaryOccurrence
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D)) :
    S.PrimitiveCrossingArrow D ≃
      Σ z : S.PrimitiveBoundaryMesh D,
        S.PrimitiveNonKilledMiddleOccurrence D
          (S.primitiveBoundaryMeshEndpoint D z) := by
  exact
    (Equiv.sumCongr
      (S.incomingCrossingArrowEquivBoundaryOccurrence D)
      (S.outgoingCrossingArrowEquivBoundaryOccurrence D H E)).trans
        (Equiv.sumSigmaDistrib (fun z : S.PrimitiveBoundaryMesh D ↦
          S.PrimitiveNonKilledMiddleOccurrence D
            (S.primitiveBoundaryMeshEndpoint D z))).symm

/-- The number of ambient crossing-arrow occurrences is the number of
ambient meshes whose translation endpoints lie on opposite sides of the
primitive deletion. -/
theorem card_primitiveCrossingArrow_eq_card_primitiveBoundaryMesh
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate
      (S.primitiveMultiplicityInput D)) :
    Nat.card (S.PrimitiveCrossingArrow D) =
      Nat.card (S.PrimitiveBoundaryMesh D) := by
  classical
  letI : Fintype (S.PrimitiveBoundaryMesh D) := Fintype.ofFinite _
  calc
    Nat.card (S.PrimitiveCrossingArrow D) =
        Nat.card
          (Σ z : S.PrimitiveBoundaryMesh D,
            S.PrimitiveNonKilledMiddleOccurrence D
              (S.primitiveBoundaryMeshEndpoint D z)) :=
      Nat.card_congr (S.crossingArrowEquivBoundaryOccurrence D H E)
    _ = ∑ z : S.PrimitiveBoundaryMesh D,
          Nat.card (S.PrimitiveNonKilledMiddleOccurrence D
            (S.primitiveBoundaryMeshEndpoint D z)) := Nat.card_sigma
    _ = ∑ _z : S.PrimitiveBoundaryMesh D, 1 := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact S.card_primitiveNonKilledMiddleOccurrence_eq_one D E z
    _ = Nat.card (S.PrimitiveBoundaryMesh D) := by
      rw [Nat.card_eq_fintype_card]
      simp

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
