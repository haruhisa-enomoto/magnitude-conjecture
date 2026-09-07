import MagnitudeConjecture.Algebra.RightModuleHoshinoTorsion
import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundary
import MagnitudeConjecture.Algebra.RightModuleSimpleTop
import MagnitudeConjecture.Algebra.RightModuleStandardMesh
import MagnitudeConjecture.Algebra.RightModuleTauAssembly
import MagnitudeConjecture.CategoryTheory.FiniteTauMatrix
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtDirectFinite
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtWeight

/-!
# The literal primitive-deletion layer

For a primitive idempotent `e`, the indecomposable modules over `A / AeA`
are already present in the ambient skeleton: they are exactly the labels on
which `AeA` acts by zero.  This file records that identification at the level
needed by the new-mesh/new-arrow argument and fixes one ambient
Krull--Schmidt multiplicity function for all subsequent counts.

No second quotient-only counting model is introduced.  In particular, the
multiplicity of a summand in a Hoshino torsion middle term is measured by the
same ambient skeleton that defines the ambient arrow multiplicities.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The ambient skeleton labels which are literal indecomposables over the
primitive quotient `A / AeA`. -/
abbrev PrimitiveQuotientLabel {e : A}
    (D : PrimitiveIdempotentData e) :=
  {x : Fin S.n // x ∈ S.primitiveKilledLabels D}

/-- A primitive-quotient label, bundled in the full subcategory of ambient
modules annihilated by `AeA`. -/
def primitiveQuotientLabelObj {e : A}
    (D : PrimitiveIdempotentData e)
    (x : S.PrimitiveQuotientLabel D) :
    PrimitiveQuotientSubcategory e :=
  ⟨S.fgObj x.1,
    (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D x.1).1 x.2⟩

/-- The deleted simple `E = S_e`, realized as the top of its primitive
projective cover. -/
abbrev primitiveDeletedSimple {e : A}
    (D : PrimitiveIdempotentData e) : FinitelyGeneratedCategory A :=
  S.projectiveSimpleTop (S.primitiveSourceProjectiveLabel D)

/-- The canonical projective-cover map onto the deleted simple. -/
abbrev primitiveDeletedSimpleProjection {e : A}
    (D : PrimitiveIdempotentData e) :
    S.fgObj (S.primitiveSourceLabel D) ⟶ S.primitiveDeletedSimple D :=
  S.projectiveSimpleTopProjection (S.primitiveSourceProjectiveLabel D)

/-- The deleted simple maps one-dimensionally into the distinguished
primitive injective. -/
theorem primitiveDeletedSimple_primitiveSinkHom_finrank_eq_one
    {e : A} {D : PrimitiveIdempotentData e}
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Module.finrank k
      (S.primitiveDeletedSimple D ⟶
        S.fgObj (S.primitiveSinkLabel D)) = 1 := by
  rw [(S.primitiveSinkHomCoordinateDualEquiv D
    (S.primitiveDeletedSimple D)).finrank_eq,
    Subspace.dual_finrank_eq,
    ← (S.primitiveSourceHomCoordinateEquiv D
      (S.primitiveDeletedSimple D)).finrank_eq]
  exact S.finrank_hom_projectiveSimpleTop_self_eq_one H
    (S.primitiveSourceProjectiveLabel D)

/-- A chosen nonzero embedding of the deleted simple into its distinguished
primitive injective. -/
def primitiveDeletedSimpleToSink {e : A}
    {D : PrimitiveIdempotentData e} [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.primitiveDeletedSimple D ⟶
      S.fgObj (S.primitiveSinkLabel D) :=
  Classical.choose
    (Module.finrank_pos_iff_exists_ne_zero.mp (by
      rw [S.primitiveDeletedSimple_primitiveSinkHom_finrank_eq_one H]
      exact Nat.zero_lt_one))

/-- The chosen map from the deleted simple to the primitive injective is
nonzero. -/
theorem primitiveDeletedSimpleToSink_ne_zero {e : A}
    {D : PrimitiveIdempotentData e} [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.primitiveDeletedSimpleToSink (D := D) H ≠ 0 :=
  Classical.choose_spec
    (Module.finrank_pos_iff_exists_ne_zero.mp (by
      rw [S.primitiveDeletedSimple_primitiveSinkHom_finrank_eq_one H]
      exact Nat.zero_lt_one))

/-- The chosen nonzero map from the simple `E` is monic. -/
theorem primitiveDeletedSimpleToSink_injective {e : A}
    {D : PrimitiveIdempotentData e} [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Function.Injective
      (S.primitiveDeletedSimpleToSink (D := D) H).hom.hom := by
  letI : IsSimpleModule Aᵐᵒᵖ (S.primitiveDeletedSimple D) :=
    S.projectiveSimpleTop_isSimpleModule
      (S.primitiveSourceProjectiveLabel D)
  apply LinearMap.injective_of_ne_zero
  intro hzero
  apply S.primitiveDeletedSimpleToSink_ne_zero (D := D) H
  apply FGModuleCat.hom_ext
  exact hzero

/-- Every map from a killed additive object to the deleted simple is zero. -/
theorem hom_to_primitiveDeletedSimple_eq_zero_of_inAdd
    {e : A} {D : PrimitiveIdempotentData e}
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (M : RightModule.FinitelyGeneratedCategory A)
    (hM : S.almostSplitSkeleton.InAdd
      (S.primitiveKilledLabels D) M)
    (f : M ⟶ S.primitiveDeletedSimple D) : f = 0 := by
  let j : S.primitiveDeletedSimple D ⟶
      S.fgObj (S.primitiveMultiplicityInput D).sink.1 :=
    S.primitiveDeletedSimpleToSink (D := D) H
  have hj : Function.Injective j.hom.hom :=
    S.primitiveDeletedSimpleToSink_injective (D := D) H
  haveI : Mono j :=
    (IndecomposableSkeleton.fg_mono_iff_injective j).2 hj
  apply (cancel_mono j).1
  rw [zero_comp]
  have hzero := S.hom_eq_zero_of_inAdd_of_noMapsToKilled
    (S.primitiveMultiplicityInput D).noMapsToKilled hM (f ≫ j)
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun q ↦ q.hom.hom x) hzero

/-- There are no maps from the deleted simple to an indecomposable module
over `A/AeA`. -/
theorem hom_primitiveDeletedSimple_to_primitiveQuotientLabel_eq_zero
    {e : A} (D : PrimitiveIdempotentData e)
    (x : S.PrimitiveQuotientLabel D)
    (f : S.primitiveDeletedSimple D ⟶ S.fgObj x.1) : f = 0 := by
  let p := S.primitiveDeletedSimpleProjection D
  haveI : Epi p :=
    S.projectiveSimpleTopProjection_epi
      (S.primitiveSourceProjectiveLabel D)
  apply (cancel_epi p).1
  have hzero :=
    PrimitiveMultiplicityInput.killed_iff_sourceHomZero
      (S := S) (S.primitiveMultiplicityInput D) x.1
      |>.1 x.2 (p ≫ f)
  change p ≫ f = 0 at hzero
  rw [hzero]
  simp

/-- Every map from the deleted simple to a killed additive object is zero. -/
theorem hom_primitiveDeletedSimple_eq_zero_of_inAdd
    {e : A} {D : PrimitiveIdempotentData e}
    (M : RightModule.FinitelyGeneratedCategory A)
    (hM : S.almostSplitSkeleton.InAdd
      (S.primitiveKilledLabels D) M)
    (f : S.primitiveDeletedSimple D ⟶ M) : f = 0 := by
  obtain ⟨W⟩ := hM
  let d : M ≅ ⨁ fun s : W.index ↦ S.fgObj (W.label s) := W.iso
  apply (cancel_mono d.hom).1
  rw [zero_comp]
  apply biproduct.hom_ext
  intro t
  rw [zero_comp]
  have hzero :=
    S.hom_primitiveDeletedSimple_to_primitiveQuotientLabel_eq_zero
      D ⟨W.label t, W.mem t⟩
        (f ≫ d.hom ≫ biproduct.π
          (fun s : W.index ↦ S.fgObj (W.label s)) t)
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun q ↦ q.hom.hom x) hzero
  simpa only [Category.assoc] using hx

/-- For an idempotent generator, the full subcategory annihilated by `AeA`
is extension closed. -/
theorem isAnnihilatedBy_primitiveIdeal_middle_of_exact
    {e : A} (he : IsIdempotentElem e)
    {Q E N : FinitelyGeneratedCategory A}
    (i : Q ⟶ E) (q : E ⟶ N)
    (hexact : Function.Exact i q)
    (hQ : IsAnnihilatedBy (primitiveIdeal e) Q)
    (hN : IsAnnihilatedBy (primitiveIdeal e) N) :
    IsAnnihilatedBy (primitiveIdeal e) E := by
  rw [isAnnihilatedBy_primitiveIdeal_iff] at hQ hN ⊢
  rw [LinearMap.exact_iff] at hexact
  intro x
  have hxker : (MulOpposite.op e) • x ∈ LinearMap.ker q.hom.hom := by
    rw [LinearMap.mem_ker]
    calc
      q ((MulOpposite.op e) • x) =
          (MulOpposite.op e) • q x := q.hom.hom.map_smul _ _
      _ = 0 := hN (q x)
  have hxrange :
      (MulOpposite.op e) • x ∈ LinearMap.range i.hom.hom :=
    hexact ▸ hxker
  obtain ⟨y, hy⟩ := hxrange
  have heop : IsIdempotentElem (MulOpposite.op e) := by
    apply MulOpposite.unop_injective
    simpa using he.eq
  have hy' : i y = (MulOpposite.op e) • x := hy
  calc
    (MulOpposite.op e) • x =
        (MulOpposite.op e) • ((MulOpposite.op e) • x) := by
      rw [← mul_smul, heop.eq]
    _ = (MulOpposite.op e) • i y := by rw [hy']
    _ = i ((MulOpposite.op e) • y) :=
      (i.hom.hom.map_smul _ _).symm
    _ = i 0 := by rw [hQ y]
    _ = 0 := i.hom.hom.map_zero

/-- Every displayed ambient decomposition of an `AeA`-annihilated module
uses only primitive-quotient labels. -/
theorem decompositionLabel_mem_primitiveKilledLabels
    {e : A} (D : PrimitiveIdempotentData e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M)
    {n : ℕ} {label : Fin n → Fin S.n}
    (d : M ≅ ⨁ fun i ↦ S.fgObj (label i)) (i : Fin n) :
    label i ∈ S.primitiveKilledLabels D := by
  let inclusion : S.fgObj (label i) ⟶ M :=
    biproduct.ι (fun j : Fin n ↦ S.fgObj (label j)) i ≫ d.inv
  have hinjective : Function.Injective inclusion :=
    (IndecomposableSkeleton.fg_mono_iff_injective inclusion).1 inferInstance
  apply (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D (label i)).2
  intro x a ha
  apply hinjective
  calc
    inclusion ((MulOpposite.op a) • x) =
        (MulOpposite.op a) • inclusion x :=
      inclusion.hom.hom.map_smul _ _
    _ = 0 := hM (inclusion x) a ha
    _ = inclusion 0 := inclusion.hom.hom.map_zero.symm

/-- Hence every `AeA`-annihilated module belongs to the additive closure of
the primitive-quotient labels in the ambient skeleton. -/
theorem inAdd_primitiveKilledLabels_of_isAnnihilatedBy
    {e : A} (D : PrimitiveIdempotentData e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    S.almostSplitSkeleton.InAdd (S.primitiveKilledLabels D) M := by
  obtain ⟨n, label, ⟨d⟩⟩ := S.fgObj_decomposition (k := k) M
  exact ⟨{
    index := FintypeCat.of (Fin n)
    label := label
    mem := S.decompositionLabel_mem_primitiveKilledLabels D M hM d
    iso := d }⟩

/-- The ambient decomposition chosen by the tau-category construction also
uses only primitive-quotient labels on an annihilated module. -/
theorem chosenLabelDecomposition_label_mem_primitiveKilledLabels
    {e : A} (D : PrimitiveIdempotentData e)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M)
    (i : Fin (S.chosenLabelDecomposition M).n) :
    (S.chosenLabelDecomposition M).label i ∈
      S.primitiveKilledLabels D :=
  S.decompositionLabel_mem_primitiveKilledLabels D M hM
    (S.chosenLabelDecomposition M).iso i

/-- Multiplicity of one ambient skeleton label in the fixed displayed
Krull--Schmidt decomposition of a finitely generated module. -/
def indecomposableMultiplicity
    (p : Fin S.n) (M : FinitelyGeneratedCategory A) : ℕ :=
  ∑ i : Fin (S.chosenLabelDecomposition M).n,
    if (S.chosenLabelDecomposition M).label i = p then 1 else 0

/-- The fixed multiplicity agrees with the occurrence count in any other
displayed decomposition into the same ambient skeleton. -/
theorem indecomposableMultiplicity_eq_of_decomposition
    (p : Fin S.n) (M : FinitelyGeneratedCategory A)
    {n : ℕ} {label : Fin n → Fin S.n}
    (d : M ≅ ⨁ fun i ↦ S.fgObj (label i)) :
    S.indecomposableMultiplicity p M =
      ∑ i : Fin n, if label i = p then 1 else 0 := by
  let T := S.finiteTauCategoryData
  let c := S.chosenLabelDecomposition M
  change (∑ i : Fin c.n, if c.label i = p then 1 else 0) = _
  exact T.label_multiplicity_eq_of_nonempty_iso_finBiproduct_obj
    p c.n n c.label label ⟨c.iso.symm.trans d⟩

/-- The fixed multiplicity agrees with a decomposition indexed by any finite
type.  This is the index-neutral form used by almost-split decompositions,
whose index is stored as a `FintypeCat`. -/
theorem indecomposableMultiplicity_eq_of_fintype_decomposition
    (p : Fin S.n) (M : FinitelyGeneratedCategory A)
    {I : Type} [Fintype I] [Finite I]
    {label : I → Fin S.n}
    (d : M ≅ ⨁ fun i : I ↦ S.fgObj (label i)) :
    S.indecomposableMultiplicity p M =
      ∑ i : I, if label i = p then 1 else 0 := by
  classical
  let ε : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let labelFin : Fin (Fintype.card I) → Fin S.n :=
    fun j ↦ label (ε.symm j)
  let factors : ∀ i : I,
      S.fgObj (labelFin (ε i)) ≅ S.fgObj (label i) := fun i ↦
    eqToIso (by simp [labelFin, ε])
  let reindex : (⨁ fun i : I ↦ S.fgObj (label i)) ≅
      ⨁ fun j : Fin (Fintype.card I) ↦ S.fgObj (labelFin j) :=
    biproduct.whiskerEquiv ε factors
  rw [S.indecomposableMultiplicity_eq_of_decomposition
    p M (d.trans reindex)]
  simpa only [labelFin, ε, Equiv.symm_apply_apply] using
    (Equiv.sum_comp ε
      (fun j ↦ if labelFin j = p then 1 else 0)).symm

/-- Ambient indecomposable multiplicity is invariant under module
isomorphism. -/
theorem indecomposableMultiplicity_iso_invariant
    (p : Fin S.n) {M N : FinitelyGeneratedCategory A}
    (d : M ≅ N) :
    S.indecomposableMultiplicity p M =
      S.indecomposableMultiplicity p N := by
  let cN := S.chosenLabelDecomposition N
  rw [S.indecomposableMultiplicity_eq_of_decomposition p M
    (d.trans cN.iso)]
  rfl

/-- Ambient indecomposable multiplicity is additive across a binary
biproduct. -/
theorem indecomposableMultiplicity_biprod
    (p : Fin S.n) (M N : FinitelyGeneratedCategory A) :
    S.indecomposableMultiplicity p (M ⊞ N) =
      S.indecomposableMultiplicity p M +
        S.indecomposableMultiplicity p N := by
  classical
  let cM := S.chosenLabelDecomposition M
  let cN := S.chosenLabelDecomposition N
  let F := fun i : Fin cM.n ↦ S.fgObj (cM.label i)
  let G := fun j : Fin cN.n ↦ S.fgObj (cN.label j)
  let label : Fin (cM.n + cN.n) → Fin S.n :=
    Fin.append cM.label cN.label
  let factors : ∀ s : Fin cM.n ⊕ Fin cN.n,
      S.fgObj (label (finSumFinEquiv s)) ≅ Sum.elim F G s := by
    intro s
    rcases s with i | j
    · exact eqToIso (by simp [label, F])
    · exact eqToIso (by simp [label, G])
  let flatten : (⨁ F) ⊞ (⨁ G) ≅
      ⨁ fun q : Fin (cM.n + cN.n) ↦ S.fgObj (label q) :=
    (FiniteRightTauCategoryData.finBiproductBiprodIsoSum F G).trans
      (biproduct.whiskerEquiv finSumFinEquiv factors)
  let d : M ⊞ N ≅
      ⨁ fun q : Fin (cM.n + cN.n) ↦ S.fgObj (label q) :=
    (biprod.mapIso cM.iso cN.iso).trans flatten
  rw [S.indecomposableMultiplicity_eq_of_decomposition p (M ⊞ N) d]
  unfold indecomposableMultiplicity
  rw [Fin.sum_univ_add]
  simp only [label, Fin.append_left, Fin.append_right]
  rfl

/-- The multiplicity of a skeleton label in one displayed indecomposable
is the corresponding Kronecker delta. -/
theorem indecomposableMultiplicity_fgObj
    (p q : Fin S.n) :
    S.indecomposableMultiplicity p (S.fgObj q) =
      if q = p then 1 else 0 := by
  let label : Fin 1 → Fin S.n := fun _ ↦ q
  let d : S.fgObj q ≅ ⨁ fun i : Fin 1 ↦ S.fgObj (label i) :=
    (biproductUniqueIso
      (fun i : Fin 1 ↦ S.fgObj (label i))).symm
  rw [S.indecomposableMultiplicity_eq_of_decomposition p (S.fgObj q) d]
  by_cases h : q = p <;> simp [label, h]

/-- At every ambient endpoint, including the projective boundary, the fixed
object multiplicity of the standard right-mesh middle term is exactly the
ambient arrow multiplicity. -/
theorem indecomposableMultiplicity_meshRightMiddle
    (p z : Fin S.n) :
    S.indecomposableMultiplicity p
        (S.meshRightAlmostSplitAt z).middle =
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p z := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let B := S.meshRightAlmostSplitAt z
  have hmiddle : (T.rightMesh (T.obj z)).X₂ = B.middle := by
    change (S.canonicalRightMesh (S.fgObj z)).X₂ = B.middle
    rw [S.canonicalRightMesh_at_label z]
    exact S.labelRightMesh_X₂ z
  let d : B.middle ≅
      ⨁ fun i ↦ T.obj
        (MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel T z i) :=
    (eqToIso hmiddle.symm).trans
      (Classical.choice
        (MagnitudeConjecture.FiniteTauMatrix.rightMiddleIso T z))
  rw [S.indecomposableMultiplicity_eq_of_decomposition p B.middle d]
  change (∑ i, if
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel T z i = p
        then 1 else 0) =
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T p z
  rw [MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity]
  congr 1
  funext i
  by_cases h :
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel T z i = p <;>
    simp [h]

/-- A label outside the primitive quotient has multiplicity zero in every
`AeA`-annihilated module. -/
theorem indecomposableMultiplicity_eq_zero_of_isAnnihilatedBy
    {e : A} (D : PrimitiveIdempotentData e)
    (p : Fin S.n) (hp : p ∉ S.primitiveKilledLabels D)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    S.indecomposableMultiplicity p M = 0 := by
  classical
  unfold indecomposableMultiplicity
  apply Finset.sum_eq_zero
  intro i _hi
  simp only [ite_eq_right_iff]
  intro hlabel
  exact (hp (hlabel ▸
    S.chosenLabelDecomposition_label_mem_primitiveKilledLabels
      D M hM i)).elim

/-- Every Hoshino torsion radical decomposes entirely into literal
primitive-quotient labels. -/
theorem primitiveTorsionFGObj_inAdd_primitiveKilledLabels
    {e : A} (D : PrimitiveIdempotentData e)
    (M : FinitelyGeneratedCategory A) :
    S.almostSplitSkeleton.InAdd (S.primitiveKilledLabels D)
      (primitiveTorsionFGObj e M) :=
  S.inAdd_primitiveKilledLabels_of_isAnnihilatedBy D _
    (primitiveTorsionFGObj_isAnnihilatedBy e M)

/-- Consequently, labels deleted from the literal quotient never occur in a
Hoshino torsion middle term. -/
theorem indecomposableMultiplicity_primitiveTorsion_eq_zero
    {e : A} (D : PrimitiveIdempotentData e)
    (p : Fin S.n) (hp : p ∉ S.primitiveKilledLabels D)
    (M : FinitelyGeneratedCategory A) :
    S.indecomposableMultiplicity p (primitiveTorsionFGObj e M) = 0 :=
  S.indecomposableMultiplicity_eq_zero_of_isAnnihilatedBy
    D p hp _ (primitiveTorsionFGObj_isAnnihilatedBy e M)

/-- The ambient Auslander--Reiten sequence at an arbitrary nonprojective
selected label, with its kernel identified with the selected translate. -/
def ambientARShortComplex
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    ShortComplex (FinitelyGeneratedCategory A) :=
  let B := S.minimalRightAlmostSplitAt z.1
  ShortComplex.mk (S.rightKernelMap z) B.map (by
    change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
      B.map = 0
    rw [Category.assoc, kernel.condition, comp_zero])

/-- Every displayed ambient Auslander--Reiten sequence is short exact. -/
theorem ambientARShortComplex_shortExact
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    (S.ambientARShortComplex z).ShortExact := by
  let B := S.minimalRightAlmostSplitAt z.1
  have hinjective : Function.Injective (S.rightKernelMap z) := by
    haveI : Mono (S.rightKernelMap z) := by
      change Mono
        ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
      infer_instance
    exact (IndecomposableSkeleton.fg_mono_iff_injective
      (S.rightKernelMap z)).1 inferInstance
  have hsurjective : Function.Surjective B.map := by
    haveI : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    exact (IndecomposableSkeleton.fg_epi_iff_surjective B.map).1
      inferInstance
  apply ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A))
  apply ModuleCat.shortComplex_shortExact
  · exact S.rightKernelMap_functionExact z
  · exact hinjective
  · exact hsurjective

/-- A right endpoint whose relative Auslander--Reiten mesh is new after
primitive deletion.  Its endpoint is an `A/AeA`-module, it is
nonprojective in that literal quotient category, and its ambient translate
lies outside the quotient subcategory. -/
structure PrimitiveNewRightMeshEndpoint {e : A}
    (D : PrimitiveIdempotentData e) where
  label : S.PrimitiveQuotientLabel D
  ambient_nonprojective : ¬ Projective (S.fgObj label.1)
  quotient_nonprojective :
    ¬ Projective (S.primitiveQuotientLabelObj D label)
  translation_not_mem :
    S.rightTranslationLabel ⟨label.1, ambient_nonprojective⟩ ∉
      S.primitiveKilledLabels D

namespace PrimitiveNewRightMeshEndpoint

variable {S} {e : A} {D : PrimitiveIdempotentData e}

/-- The endpoint as an ambient nonprojective label. -/
def ambientLabel (N : S.PrimitiveNewRightMeshEndpoint D) :
    {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
  ⟨N.label.1, N.ambient_nonprojective⟩

/-- The deleted ambient translate `q_N = τ_A N`, bundled as a surviving
label of the factor category `mod A / [mod (A/AeA)]`. -/
def rightMarker (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.SurvivingLabel (S.primitiveKilledLabels D) :=
  ⟨S.rightTranslationLabel N.ambientLabel, N.translation_not_mem⟩

/-- The marker `q_N = τ_A N` is tau-injective in the factor category: its
ambient inverse translate is the quotient label `N`, which is killed in the
factor. -/
theorem rightMarker_isInjective
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).IsInjective
      N.rightMarker := by
  let K := S.primitiveKilledLabels D
  let z := N.ambientLabel
  let y : {y : Fin S.n // ¬ Injective (S.fgObj y)} :=
    S.rightTranslation z
  let x := (S.rightTranslationEquiv).symm y
  have hx : x.1 = N.label.1 := by
    exact congrArg Subtype.val (S.rightTranslationEquiv.symm_apply_apply z)
  have hxK : x.1 ∈ K := by
    change x.1 ∈ S.primitiveKilledLabels D
    rw [hx]
    exact N.label.2
  let T := S.labelLeftMesh N.rightMarker.1
  have hnotInjective : ¬ Injective (S.fgObj N.rightMarker.1) := by
    change ¬ Injective (S.fgObj (S.rightTranslation z).1)
    exact (S.rightTranslation z).2
  let eT : T.X₃ ≅ S.fgObj x.1 := by
    convert Iso.refl (S.fgObj x.1) using 1
    simp [T, labelLeftMesh, hnotInjective, noninjectiveLeftMesh,
      x, y, z, almostSplitSkeleton]
    congr 2
  let eQ :
      (S.factorRawLeftMesh K N.rightMarker.1).X₃ ≅
        (S.factorModuleFunctor K).obj (S.fgObj x.1) :=
    (S.factorModuleFunctor K).mapIso eT
  have htarget : IsZero
      ((S.factorModuleFunctor K).obj (S.fgObj x.1)) :=
    (S.factorObject_isZero_of_mem K hxK).of_iso
      (S.factorAmbientPointIsoFactorModule K x.1)
  have hraw : IsZero (S.factorRawLeftMesh K N.rightMarker.1).X₃ :=
    htarget.of_iso eQ
  change IsZero
    (S.canonicalFactorLeftMesh K
      (S.factorObject K N.rightMarker)).X₃
  rw [S.canonicalFactorLeftMesh_at_label K N.rightMarker]
  rw [factorLabelLeftMesh]
  simp only [dif_pos (Or.inl hraw), factorZeroRightLeftMesh]
  exact S.factorZeroObject_isZero K

/-- The factor-injective boundary label supplied by a new mesh endpoint. -/
def rightMarkerInjectiveLabel
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.FactorInjectiveLabel (S.primitiveKilledLabels D) :=
  ⟨N.rightMarker, N.rightMarker_isInjective⟩

/-- The boundary coordinate theorem gives the marker multiplicity
`[q_N : S_e] = 1`. -/
theorem rightMarker_primitiveMultiplicity_eq_one
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveMultiplicity D N.rightMarker.1 = 1 :=
  B.injective_multiplicity_eq_one N.rightMarkerInjectiveLabel

/-- The manuscript's positive boundary test, expressed in the form used by
the new-arrow construction: `Hom_A(S_e,q_N)=0`.  Complementarity with the
left marker is proved at the later boundary-correspondence layer. -/
def IsPositive
    (N : S.PrimitiveNewRightMeshEndpoint D) : Prop :=
  ∀ f : S.primitiveDeletedSimple D ⟶
      S.fgObj N.rightMarker.1, f = 0

/-- At a positive new mesh, the deleted simple has no map to the ambient AR
middle term. -/
theorem hom_primitiveDeletedSimple_to_ambientMiddle_eq_zero
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive)
    (f : S.primitiveDeletedSimple D ⟶
      (S.minimalRightAlmostSplitAt N.label.1).middle) :
    f = 0 := by
  let T := S.ambientARShortComplex N.ambientLabel
  have hT : T.ShortExact := S.ambientARShortComplex_shortExact N.ambientLabel
  letI : Mono T.f := hT.mono_f
  have htarget : f ≫ T.g = 0 := by
    apply S.hom_primitiveDeletedSimple_to_primitiveQuotientLabel_eq_zero
      D N.label
  let lift : S.primitiveDeletedSimple D ⟶ T.X₁ :=
    hT.exact.lift f htarget
  have hlift : lift = 0 := by
    exact hpositive lift
  calc
    f = lift ≫ T.f := (hT.exact.lift_f f htarget).symm
    _ = 0 := by rw [hlift, zero_comp]

/-- The Hoshino torsion radical of the ambient translate is the source of
the new relative mesh. -/
abbrev sourceModule (N : S.PrimitiveNewRightMeshEndpoint D) :
    FinitelyGeneratedCategory A :=
  primitiveTorsionFGObj e
    (S.fgObj (S.rightTranslationLabel N.ambientLabel))

/-- The middle term of the new relative mesh is the torsion radical of the
ambient right almost-split middle term. -/
abbrev middleModule (N : S.PrimitiveNewRightMeshEndpoint D) :
    FinitelyGeneratedCategory A :=
  primitiveTorsionFGObj e
    (S.minimalRightAlmostSplitAt N.label.1).middle

/-- Ambient injectivity of the transported AR-kernel inclusion. -/
theorem rightKernelMap_injective
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Function.Injective (S.rightKernelMap N.ambientLabel) := by
  let z := N.ambientLabel
  let B := S.minimalRightAlmostSplitAt z.1
  haveI : Mono (S.rightKernelMap N.ambientLabel) := by
    change Mono
      ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
    infer_instance
  exact (IndecomposableSkeleton.fg_mono_iff_injective
    (S.rightKernelMap N.ambientLabel)).1 inferInstance

/-- The ambient FG-module short complex underlying the new relative mesh.
Its terms are `R(τ_A N)`, `R(V_N)`, and `N`. -/
def fgShortComplex (N : S.PrimitiveNewRightMeshEndpoint D) :
    ShortComplex (FinitelyGeneratedCategory A) :=
  ShortComplex.mk
    (primitiveTorsionMap e (S.rightKernelMap N.ambientLabel))
    (primitiveTorsionAmbientTargetMap e
      (S.minimalRightAlmostSplitAt N.label.1).map)
    (primitiveTorsion_comp_eq_zero e
      (S.rightKernelMap N.ambientLabel)
      (S.minimalRightAlmostSplitAt N.label.1).map
      N.rightKernelMap_injective
      (S.rightKernelMap_functionExact N.ambientLabel))

/-- Hoshino's comparison makes the displayed new relative mesh short
exact. -/
theorem fgShortComplex_shortExact
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.fgShortComplex.ShortExact := by
  exact primitiveTorsion_fg_shortExact_of_not_projective
    (k := k) e
      ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D N.label.1).1
        N.label.2)
      (S.rightKernelMap N.ambientLabel)
      (S.minimalRightAlmostSplitAt N.label.1).map
      N.rightKernelMap_injective
      (S.rightKernelMap_functionExact N.ambientLabel)
      (S.minimalRightAlmostSplitAt N.label.1).rightAlmostSplit
      N.quotient_nonprojective

/-- The Hoshino torsion kernel which starts the new relative mesh is not
injective even in the ambient module category. -/
theorem sourceModule_not_injective
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ¬ Injective N.sourceModule := by
  let B := S.minimalRightAlmostSplitAt N.label.1
  have hnotSplit : ¬ IsSplitEpi N.fgShortComplex.g := by
    intro hsplit
    have hright : IsRightAlmostSplit
        (primitiveTorsionTargetMap e
          ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
            D N.label.1).1 N.label.2)
          B.map) :=
      primitiveTorsionTargetMap_isRightAlmostSplit e
        ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
          D N.label.1).1 N.label.2)
        B.map B.rightAlmostSplit
    apply hright.not_isSplitEpi
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    exact IsSplitEpi.mk' {
      section_ := ObjectProperty.homMk s.section_
      id := by
        apply ObjectProperty.hom_ext
        exact s.id }
  intro hInjective
  letI : Injective N.sourceModule := hInjective
  letI : Injective N.fgShortComplex.X₁ := by
    change Injective N.sourceModule
    infer_instance
  let splitting := N.fgShortComplex_shortExact.splittingOfInjective
  exact hnotSplit splitting.isSplitEpi_g

/-- The source label selected from Hoshino's indecomposable torsion
radical. -/
def sourceAmbientLabel [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) : Fin S.n :=
  Classical.choose
    (S.almostSplitSkeleton.complete N.sourceModule
      (S.primitiveTorsionFGObj_rightTranslation_isIndecomposableModule
        H he N.ambientLabel
        ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
          D N.label.1).1 N.label.2)
        N.quotient_nonprojective))

/-- The selected source label represents the actual torsion kernel
`R(τ_A N)`. -/
def sourceIso [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.sourceModule ≅ S.fgObj (N.sourceAmbientLabel H he) :=
  (Classical.choose_spec
    (S.almostSplitSkeleton.complete N.sourceModule
      (S.primitiveTorsionFGObj_rightTranslation_isIndecomposableModule
        H he N.ambientLabel
        ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
          D N.label.1).1 N.label.2)
        N.quotient_nonprojective))).some

/-- The source of a new relative mesh is itself a literal
`A/AeA`-indecomposable. -/
theorem sourceAmbientLabel_mem [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.sourceAmbientLabel H he ∈ S.primitiveKilledLabels D := by
  apply S.almostSplitSkeleton.index_mem_of_retract_inAdd
    (Retract.ofIso (N.sourceIso H he).symm)
  exact S.primitiveTorsionFGObj_inAdd_primitiveKilledLabels D
    (S.fgObj (S.rightTranslationLabel N.ambientLabel))

/-- The selected ambient source label is noninjective. -/
theorem sourceAmbientLabel_not_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ¬ Injective (S.fgObj (N.sourceAmbientLabel H he)) := by
  intro hInjective
  apply N.sourceModule_not_injective
  exact Injective.of_iso (N.sourceIso H he).symm hInjective

/-- The source `M` of the new relative mesh, bundled in the same literal
quotient label type as its endpoint `N`. -/
def sourceLabel [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.PrimitiveQuotientLabel D :=
  ⟨N.sourceAmbientLabel H he, N.sourceAmbientLabel_mem H he⟩

/-- The source `M` as an ambient noninjective label, so that its inverse
Auslander--Reiten translate is defined. -/
def sourceNoninjectiveLabel [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
  ⟨N.sourceAmbientLabel H he,
    N.sourceAmbientLabel_not_injective H he⟩

/-- The ambient inverse-translation label underlying the manuscript's left
marker `p_M = τ_A⁻¹M`.  The later boundary theorem proves that it lies
outside the primitive quotient label set. -/
def leftMarkerAmbientLabel [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) : Fin S.n :=
  ((S.rightTranslationEquiv).symm
    (N.sourceNoninjectiveLabel H he)).1

/-- Relative arrow multiplicity into `N`, computed in the existing ambient
skeleton from the Hoshino torsion middle term. -/
def relativeArrowMultiplicity
    (source : S.PrimitiveQuotientLabel D)
    (N : S.PrimitiveNewRightMeshEndpoint D) : ℕ :=
  S.indecomposableMultiplicity source.1 N.middleModule

end PrimitiveNewRightMeshEndpoint

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
