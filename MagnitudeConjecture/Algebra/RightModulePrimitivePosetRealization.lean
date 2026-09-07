import MagnitudeConjecture.Algebra.RightModulePrimitiveMultiplicity
import MagnitudeConjecture.Algebra.RightModuleDirected
import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace
import MagnitudeConjecture.Combinatorics.PosetSpaceSharpEquality

/-!
# Poset-space realization data for a primitive factor

This file specializes the concrete representable poset-space functor to the
literal primitive factor category.  The primitive multiplicity package already
supplies finite-dimensional represented Hom spaces and faithfulness of
`Hom(P, -)`.  Consequently the only remaining realization input is the
manuscript's projective-poset presentation together with Iyama fullness and
essential surjectivity.

The repaired manuscript derives the concrete `T`-space model from Iyama's
minimal realization: restricted Yoneda lands in modules over the boundary
projective incidence category, and the projective-socle condition identifies
its image with subspace representations.  The structures below isolate the
remaining fullness and object-realization part of that derivation.  They are
not hypotheses of the eventual public magnitude theorem.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The finite type of tau-projective surviving labels in a literal factor. -/
abbrev FactorProjectiveLabel (K : Set (Fin S.n)) :=
  {x : S.SurvivingLabel K //
    (S.factorFiniteTauCategoryData K).IsProjective x}

/-- The finite type of tau-injective surviving labels in a literal factor. -/
abbrev FactorInjectiveLabel (K : Set (Fin S.n)) :=
  {x : S.SurvivingLabel K //
    (S.factorFiniteTauCategoryData K).IsInjective x}

/-- Primitive multiplicity data makes the distinguished source a literal
tau-projective label of the factor. -/
def PrimitiveMultiplicityInput.sourceProjectiveLabel
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    S.FactorProjectiveLabel K :=
  ⟨D.source, D.toPrimitiveTraceInput.toPrimitiveFactorInput.source_isProjective⟩

/-- Primitive multiplicity data makes the distinguished sink a literal
tau-injective label of the factor. -/
def PrimitiveMultiplicityInput.sinkInjectiveLabel
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    S.FactorInjectiveLabel K :=
  ⟨D.sink, D.toPrimitiveTraceInput.toPrimitiveFactorInput.sink_isInjective⟩

/-- Finrank form of the primitive multiplicity identity in the literal
factor. -/
theorem PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K x) =
        D.multiplicity x.1 := by
  calc
    Module.finrank k
        (S.factorObject K D.source ⟶ S.factorObject K x) =
        Module.finrank k (S.fgObj D.source.1 ⟶ S.fgObj x.1) :=
      (S.factorHomFromLinearEquiv D.noMapsFromKilled x).finrank_eq.symm
    _ = D.multiplicity x.1 := (D.multiplicity_eq_sourceHom x.1).symm

/-- Dual finrank form of the primitive multiplicity identity in the literal
factor. -/
theorem PrimitiveMultiplicityInput.factorHomTo_finrank_eq_multiplicity
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    Module.finrank k
      (S.factorObject K x ⟶ S.factorObject K D.sink) =
        D.multiplicity x.1 := by
  calc
    Module.finrank k
        (S.factorObject K x ⟶ S.factorObject K D.sink) =
        Module.finrank k (S.fgObj x.1 ⟶ S.fgObj D.sink.1) :=
      (S.factorHomToLinearEquiv D.noMapsToKilled x).finrank_eq.symm
    _ = D.multiplicity x.1 := (D.multiplicity_eq_sinkHom x.1).symm

/-- Every surviving factor label receives a nonzero map from the primitive
source. -/
theorem PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K) :
    ∃ h : S.factorObject K D.source ⟶ S.factorObject K x, h ≠ 0 := by
  apply (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp
  rw [D.factorHomFrom_finrank_eq_multiplicity]
  exact PrimitiveMultiplicityInput.multiplicity_pos (S := S) D x

/-- Postcomposition on the represented factor Hom space. -/
def PrimitiveMultiplicityInput.sourcePostcomposition
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    {X Y : S.FactorCategory K} (f : X ⟶ Y) :
    (S.factorObject K D.source ⟶ X) →ₗ[k]
      (S.factorObject K D.source ⟶ Y) where
  toFun h := h ≫ f
  map_add' h g := by simp
  map_smul' a h := by simp

/-- Between multiplicity-one objects, every nonzero factor morphism induces
an injective map on represented Hom. -/
theorem PrimitiveMultiplicityInput.sourcePostcomposition_injective
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    {x y : S.SurvivingLabel K}
    (hx : D.multiplicity x.1 = 1) (hy : D.multiplicity y.1 = 1)
    (f : S.factorObject K x ⟶ S.factorObject K y) (hf : f ≠ 0) :
    Function.Injective
      (PrimitiveMultiplicityInput.sourcePostcomposition (S := S) D f) := by
  have hmap :
      PrimitiveMultiplicityInput.sourcePostcomposition (S := S) D f ≠ 0 := by
    intro hzero
    apply hf
    apply D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
      f 0
    intro h
    have happ := LinearMap.congr_fun hzero h
    change h ≫ f = 0 at happ
    simpa using happ
  have hsource : Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K x) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D x).trans hx
  have htarget : Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K y) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D y).trans hy
  have hsurj : Function.Surjective
      (PrimitiveMultiplicityInput.sourcePostcomposition (S := S) D f) :=
    surjective_of_nonzero_of_finrank_eq_one htarget hmap
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsource.trans htarget.symm)).mpr hsurj

/-- The composite of nonzero maps between multiplicity-one factor objects is
nonzero.  This is the paper's faithfulness-plus-nonzero-scalars argument. -/
theorem PrimitiveMultiplicityInput.comp_ne_zero_of_multiplicity_eq_one
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    {x y z : S.SurvivingLabel K}
    (hx : D.multiplicity x.1 = 1)
    (hy : D.multiplicity y.1 = 1)
    (hz : D.multiplicity z.1 = 1)
    (f : S.factorObject K x ⟶ S.factorObject K y) (hf : f ≠ 0)
    (g : S.factorObject K y ⟶ S.factorObject K z) (hg : g ≠ 0) :
    f ≫ g ≠ 0 := by
  obtain ⟨a, ha⟩ :=
    PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero (S := S) D x
  have hfinj := PrimitiveMultiplicityInput.sourcePostcomposition_injective
    (S := S) D hx hy f hf
  have hginj := PrimitiveMultiplicityInput.sourcePostcomposition_injective
    (S := S) D hy hz g hg
  have haf : a ≫ f ≠ 0 := by
    intro hzero
    apply ha
    apply hfinj
    change a ≫ f = (0 : S.factorObject K D.source ⟶
      S.factorObject K x) ≫ f
    simpa using hzero
  have hafg : (a ≫ f) ≫ g ≠ 0 := by
    intro hzero
    apply haf
    apply hginj
    change (a ≫ f) ≫ g =
      (0 : S.factorObject K D.source ⟶ S.factorObject K y) ≫ g
    simpa using hzero
  intro hzero
  apply hafg
  rw [Category.assoc, hzero, comp_zero]

/-- Tau-projective labels other than the distinguished root. -/
abbrev NonSourceFactorProjectiveLabel
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :=
  {p : S.FactorProjectiveLabel K // p ≠ D.sourceProjectiveLabel}

/-- The exact directed boundary input preceding the poset-space realization
in the frozen manuscript. -/
structure PrimitiveDirectedBoundaryData
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) where
  acyclic : S.HasAcyclicNonzeroNonisomorphisms
  projective_multiplicity_eq_one :
    ∀ p : S.FactorProjectiveLabel K, D.multiplicity p.1.1 = 1
  injective_multiplicity_eq_one :
    ∀ i : S.FactorInjectiveLabel K, D.multiplicity i.1.1 = 1

namespace PrimitiveDirectedBoundaryData

variable {S} {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The non-root projective labels, tagged by the boundary data that proves
their Hom relation is an order. -/
def ProjectivePoset (B : S.PrimitiveDirectedBoundaryData D) : Type u :=
  ULift.{u} (S.NonSourceFactorProjectiveLabel D)

noncomputable instance projectivePosetFintype
    (B : S.PrimitiveDirectedBoundaryData D) : Fintype B.ProjectivePoset :=
  Fintype.ofEquiv (S.NonSourceFactorProjectiveLabel D) Equiv.ulift.symm

/-- Reverse nonzero-Hom reachability on the non-root projectives. -/
def projectiveLE (B : S.PrimitiveDirectedBoundaryData D)
    (s t : B.ProjectivePoset) : Prop :=
  ∃ f : S.factorObject K t.down.1.1 ⟶
    S.factorObject K s.down.1.1, f ≠ 0

private theorem projectiveLE_refl
    (B : S.PrimitiveDirectedBoundaryData D)
    (s : B.ProjectivePoset) :
    B.projectiveLE s s := by
  refine ⟨CategoryStruct.id (S.factorObject K s.down.1.1), ?_⟩
  intro hzero
  exact S.factorObject_not_isZero K s.down.1.1
    ((IsZero.iff_id_eq_zero _).2 hzero)

private theorem projectiveLE_trans
    (B : S.PrimitiveDirectedBoundaryData D)
    {r s t : B.ProjectivePoset}
    (hrs : B.projectiveLE r s) (hst : B.projectiveLE s t) :
    B.projectiveLE r t := by
  obtain ⟨f, hf⟩ := hrs
  obtain ⟨g, hg⟩ := hst
  refine ⟨g ≫ f, ?_⟩
  exact PrimitiveMultiplicityInput.comp_ne_zero_of_multiplicity_eq_one
    (S := S) D
    (B.projective_multiplicity_eq_one t.down.1)
    (B.projective_multiplicity_eq_one s.down.1)
    (B.projective_multiplicity_eq_one r.down.1) g hg f hf

private theorem projectiveLE_antisymm
    (B : S.PrimitiveDirectedBoundaryData D)
    {s t : B.ProjectivePoset}
    (hst : B.projectiveLE s t) (hts : B.projectiveLE t s) : s = t := by
  obtain ⟨f, hf⟩ := hst
  obtain ⟨g, hg⟩ := hts
  have hlabel : t.down.1.1 = s.down.1.1 :=
    HasAcyclicNonzeroNonisomorphisms.factorObject_label_eq_of_two_way
      (S := S) B.acyclic K t.down.1.1 s.down.1.1 f hf g hg
  apply ULift.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hlabel.symm

/-- The literal Hom relation is a partial order on the non-root
tau-projectives. -/
@[reducible] noncomputable def projectivePartialOrder
    (B : S.PrimitiveDirectedBoundaryData D) :
    PartialOrder B.ProjectivePoset where
  le := B.projectiveLE
  lt := fun s t ↦ B.projectiveLE s t ∧ ¬ B.projectiveLE t s
  le_refl := B.projectiveLE_refl
  le_trans := fun _ _ _ ↦ B.projectiveLE_trans
  le_antisymm := fun _ _ ↦ B.projectiveLE_antisymm
  lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl

noncomputable instance projectivePosetPartialOrder
    (B : S.PrimitiveDirectedBoundaryData D) :
    PartialOrder B.ProjectivePoset :=
  B.projectivePartialOrder

end PrimitiveDirectedBoundaryData

/-- The manuscript's presentation of all tau-projectives as the root `P`
together with the projectives `P_t`, indexed by a finite poset `T`.

The field `order_iff_nonzero` is the literal order
`s ≤ t ↔ Q(P_t,P_s) ≠ 0`.  The chosen nonzero maps `unit t : P ⟶ P_t`
and their factorization property are precisely the data used by the concrete
representable functor. -/
structure PrimitiveProjectivePosetData
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (T : Type u) [Fintype T] [PartialOrder T] where
  projectiveEquiv : S.FactorProjectiveLabel K ≃ Option T
  source_eq_none : projectiveEquiv D.sourceProjectiveLabel = none
  projective_multiplicity_eq_one :
    ∀ p : S.FactorProjectiveLabel K, D.multiplicity p.1.1 = 1
  order_iff_nonzero : ∀ s t : T,
    s ≤ t ↔ ∃ f :
      S.factorObject K (projectiveEquiv.symm (some t)).1 ⟶
        S.factorObject K (projectiveEquiv.symm (some s)).1,
      f ≠ 0
  unit : ∀ t : T,
    S.factorObject K D.source ⟶
      S.factorObject K (projectiveEquiv.symm (some t)).1
  unit_ne_zero : ∀ t, unit t ≠ 0
  factor : ∀ {s t : T}, s ≤ t →
    ∃ v :
      S.factorObject K (projectiveEquiv.symm (some t)).1 ⟶
        S.factorObject K (projectiveEquiv.symm (some s)).1,
      unit t ≫ v = unit s

namespace PrimitiveDirectedBoundaryData

variable {S} {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The canonical enumeration of all projectives by the root plus the
non-root projective poset. -/
noncomputable def projectiveEquiv
    (B : S.PrimitiveDirectedBoundaryData D) :
    S.FactorProjectiveLabel K ≃ Option B.ProjectivePoset := by
  classical
  exact (Equiv.optionSubtypeNe D.sourceProjectiveLabel).symm |>.trans
    (Equiv.optionCongr Equiv.ulift.symm)

@[simp]
theorem projectiveEquiv_source
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.projectiveEquiv D.sourceProjectiveLabel = none := by
  classical
  simp [projectiveEquiv]

@[simp]
theorem projectiveEquiv_symm_some
    (B : S.PrimitiveDirectedBoundaryData D) (t : B.ProjectivePoset) :
    B.projectiveEquiv.symm (some t) = t.down.1 := by
  rfl

/-- A chosen nonzero map `P ⟶ P_t`, obtained from positivity of the
primitive multiplicity. -/
noncomputable def unit (B : S.PrimitiveDirectedBoundaryData D)
    (t : B.ProjectivePoset) :
    S.factorObject K D.source ⟶ S.factorObject K t.down.1.1 :=
  Classical.choose
    (PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero
      (S := S) D t.down.1.1)

theorem unit_ne_zero (B : S.PrimitiveDirectedBoundaryData D)
    (t : B.ProjectivePoset) : B.unit t ≠ 0 :=
  Classical.choose_spec
    (PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero
      (S := S) D t.down.1.1)

/-- In the one-dimensional represented Hom space, the nonzero composite
`P ⟶ P_t ⟶ P_s` is a scalar multiple of the chosen `P ⟶ P_s`;
rescaling the second map gives the required literal factorization. -/
theorem exists_unit_factor
    (B : S.PrimitiveDirectedBoundaryData D)
    {s t : B.ProjectivePoset} (hst : s ≤ t) :
    ∃ v : S.factorObject K t.down.1.1 ⟶
      S.factorObject K s.down.1.1,
      B.unit t ≫ v = B.unit s := by
  change B.projectiveLE s t at hst
  obtain ⟨v, hv⟩ := hst
  have hcomp : B.unit t ≫ v ≠ 0 :=
    PrimitiveMultiplicityInput.comp_ne_zero_of_multiplicity_eq_one
      (S := S) D
      (B.projective_multiplicity_eq_one D.sourceProjectiveLabel)
      (B.projective_multiplicity_eq_one t.down.1)
      (B.projective_multiplicity_eq_one s.down.1)
      (B.unit t) (B.unit_ne_zero t) v hv
  have hfinrank : Module.finrank k
      (S.factorObject K D.source ⟶
        S.factorObject K s.down.1.1) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D s.down.1.1).trans
        (B.projective_multiplicity_eq_one s.down.1)
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hfinrank hcomp (B.unit s)
  refine ⟨c • v, ?_⟩
  simpa using hc

/-- Directedness and boundary multiplicity one construct the complete
projective-poset presentation used by the representable functor. -/
noncomputable def projectivePosetData
    (B : S.PrimitiveDirectedBoundaryData D) :
    S.PrimitiveProjectivePosetData D B.ProjectivePoset where
  projectiveEquiv := B.projectiveEquiv
  source_eq_none := B.projectiveEquiv_source
  projective_multiplicity_eq_one := B.projective_multiplicity_eq_one
  order_iff_nonzero := fun _ _ ↦ Iff.rfl
  unit := B.unit
  unit_ne_zero := B.unit_ne_zero
  factor := B.exists_unit_factor

end PrimitiveDirectedBoundaryData

namespace PrimitiveProjectivePosetData

variable {S} {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- The selected surviving label underlying `P_t`. -/
abbrev label (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    S.SurvivingLabel K :=
  (R.projectiveEquiv.symm (some t)).1

/-- The `P_t` indexed by the projective poset. -/
abbrev projective (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    S.FactorCategory K :=
  S.factorObject K (R.label t)

/-- The projective enumeration proves the manuscript's count
`p = |T| + 1`. -/
theorem card_factorProjectiveLabel
    (R : S.PrimitiveProjectivePosetData D T) :
    Fintype.card (S.FactorProjectiveLabel K) = Fintype.card T + 1 := by
  rw [Fintype.card_congr R.projectiveEquiv]
  exact Fintype.card_option

/-- The projective-poset presentation instantiates the manuscript's concrete
representable `T`-space data on the literal factor category. -/
def representableData (R : S.PrimitiveProjectivePosetData D T) :
    PosetSpace.RepresentableData k T (S.FactorCategory K) where
  source := S.factorObject K D.source
  projective := R.projective
  unit := R.unit
  factor := R.factor
  homFinite := fun X ↦ S.factorCategoryHomFinite K _ X

/-- The represented Hom functor of a primitive factor is faithful; no
faithfulness field remains in the Iyama realization input below. -/
theorem representable_faithful
    (R : S.PrimitiveProjectivePosetData D T) :
    R.representableData.functor.Faithful :=
  R.representableData.faithful
    D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful

/-- The chosen boundary map `P ⟶ P_t` spans the one-dimensional represented
Hom space. -/
theorem exists_smul_unit_eq
    (R : S.PrimitiveProjectivePosetData D T) (t : T)
    (h : S.factorObject K D.source ⟶ S.factorObject K (R.label t)) :
    ∃ c : k, c • R.unit t = h := by
  have hfinrank : Module.finrank k
      (R.representableData.source ⟶ R.projective t) = 1 := by
    change Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K (R.label t)) = 1
    exact
      (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
        (S := S) D (R.label t)).trans
        (R.projective_multiplicity_eq_one
          (R.projectiveEquiv.symm (some t)))
  exact exists_smul_eq_of_finrank_eq_one hfinrank (R.unit_ne_zero t) h

/-- Precomposition with `P ⟶ P_t` is injective.  This is the manuscript's
faithfulness argument, with the scalar spanning step made explicit. -/
theorem precomposition_injective
    (R : S.PrimitiveProjectivePosetData D T) (t : T)
    (X : S.FactorCategory K) :
    Function.Injective (R.representableData.precomposition t X) := by
  intro f g hfg
  apply D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
    f g
  intro h
  change S.factorObject K D.source ⟶
    S.factorObject K (R.label t) at h
  obtain ⟨c, hc⟩ := R.exists_smul_unit_eq t h
  change R.unit t ≫ f = R.unit t ≫ g at hfg
  calc
    h ≫ f = (c • R.unit t) ≫ f :=
      congrArg (fun q ↦ q ≫ f) hc.symm
    _ = c • (R.unit t ≫ f) := Linear.smul_comp _ _ _ _ _ _
    _ = c • (R.unit t ≫ g) := congrArg (c • ·) hfg
    _ = (c • R.unit t) ≫ g := (Linear.smul_comp _ _ _ _ _ _).symm
    _ = h ≫ g := congrArg (fun q ↦ q ≫ g) hc

/-- The represented subspace at `t` has the same dimension as
`Hom(P_t,X)`, because its defining precomposition map is injective. -/
theorem finrank_subspace_eq_projectiveHom
    (R : S.PrimitiveProjectivePosetData D T) (t : T)
    (X : S.FactorCategory K) :
    Module.finrank k ((R.representableData.obj X).subspace t) =
      Module.finrank k (R.projective t ⟶ X) := by
  change Module.finrank k
      (LinearMap.range (R.representableData.precomposition t X)) =
    Module.finrank k (R.projective t ⟶ X)
  exact LinearMap.finrank_range_of_inj (R.precomposition_injective t X)

/-- Every Hom space between two non-root projectives has dimension at most
one.  It injects into the one-dimensional represented Hom space of its
target. -/
theorem projectiveHom_finrank_le_one
    (R : S.PrimitiveProjectivePosetData D T) (s t : T) :
    Module.finrank k (R.projective t ⟶ R.projective s) ≤ 1 := by
  have hinj := R.precomposition_injective t (R.projective s)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have htarget : Module.finrank k
      (R.representableData.source ⟶ R.projective s) = 1 := by
    change Module.finrank k
      (S.factorObject K D.source ⟶ S.factorObject K (R.label s)) = 1
    exact
      (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
        (S := S) D (R.label s)).trans
        (R.projective_multiplicity_eq_one
          (R.projectiveEquiv.symm (some s)))
  exact hle.trans_eq htarget

/-- The normalized incidence morphism `P_t ⟶ P_s` for `s ≤ t`. -/
noncomputable def incidenceMap
    (R : S.PrimitiveProjectivePosetData D T) {s t : T} (hst : s ≤ t) :
    R.projective t ⟶ R.projective s :=
  Classical.choose (R.factor hst)

@[reassoc]
theorem unit_comp_incidenceMap
    (R : S.PrimitiveProjectivePosetData D T) {s t : T} (hst : s ≤ t) :
    R.unit t ≫ R.incidenceMap hst = R.unit s :=
  Classical.choose_spec (R.factor hst)

/-- A normalized incidence morphism is nonzero. -/
theorem incidenceMap_ne_zero
    (R : S.PrimitiveProjectivePosetData D T) {s t : T} (hst : s ≤ t) :
    R.incidenceMap hst ≠ 0 := by
  intro hzero
  apply R.unit_ne_zero s
  rw [← R.unit_comp_incidenceMap hst, hzero, comp_zero]

/-- Normalization by the chosen maps from `P` determines an incidence
morphism uniquely. -/
theorem incidenceMap_unique
    (R : S.PrimitiveProjectivePosetData D T) {s t : T} (hst : s ≤ t)
    (f : R.projective t ⟶ R.projective s)
    (hf : R.unit t ≫ f = R.unit s) :
    f = R.incidenceMap hst := by
  apply R.precomposition_injective t (R.projective s)
  exact hf.trans (R.unit_comp_incidenceMap hst).symm

/-- The normalized incidence maps have literal incidence composition. -/
theorem incidenceMap_comp
    (R : S.PrimitiveProjectivePosetData D T)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) :
    R.incidenceMap hst ≫ R.incidenceMap hrs =
      R.incidenceMap (hrs.trans hst) := by
  apply R.incidenceMap_unique (hrs.trans hst)
  rw [← Category.assoc, R.unit_comp_incidenceMap hst,
    R.unit_comp_incidenceMap hrs]

/-- Every morphism along an incidence relation is a scalar multiple of the
normalized incidence morphism. -/
theorem exists_smul_incidenceMap_eq
    (R : S.PrimitiveProjectivePosetData D T)
    {s t : T} (hst : s ≤ t) (f : R.projective t ⟶ R.projective s) :
    ∃ c : k, c • R.incidenceMap hst = f := by
  have hpos : 0 < Module.finrank k
      (R.projective t ⟶ R.projective s) :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k)).2
      ⟨R.incidenceMap hst, R.incidenceMap_ne_zero hst⟩
  have hone : Module.finrank k
      (R.projective t ⟶ R.projective s) = 1 := by
    have hle := R.projectiveHom_finrank_le_one s t
    omega
  exact exists_smul_eq_of_finrank_eq_one hone
    (R.incidenceMap_ne_zero hst) f

/-- Off the incidence order there are no morphisms between the corresponding
projectives. -/
theorem eq_zero_of_projectiveHom_of_not_le
    (R : S.PrimitiveProjectivePosetData D T)
    {s t : T} (hst : ¬ s ≤ t) (f : R.projective t ⟶ R.projective s) :
    f = 0 := by
  by_contra hf
  exact hst ((R.order_iff_nonzero s t).2 ⟨f, hf⟩)

/-- Scalar multiplication of the chosen `P ⟶ P_t` map, as a linear map
from the coefficient field. -/
def unitScalarLinearMap
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    k →ₗ[k] (S.factorObject K D.source ⟶ S.factorObject K (R.label t)) where
  toFun c := c • R.unit t
  map_add' c d := add_smul c d (R.unit t)
  map_smul' c d := by
    change (c * d) • R.unit t = c • d • R.unit t
    rw [smul_smul]

/-- The chosen boundary map identifies `Hom(P,P_t)` with the coefficient
field. -/
noncomputable def unitCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    (S.factorObject K D.source ⟶ S.factorObject K (R.label t)) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (R.unitScalarLinearMap t) ⟨by
    intro c d hcd
    change c • R.unit t = d • R.unit t at hcd
    have hzero : (c - d) • R.unit t = 0 := by
      rw [sub_smul, hcd, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right
      (R.unit_ne_zero t)),
    fun h ↦ R.exists_smul_unit_eq t h⟩).symm

@[simp]
theorem unitCoordinateEquiv_symm_apply
    (R : S.PrimitiveProjectivePosetData D T) (t : T) (c : k) :
    (R.unitCoordinateEquiv t).symm c = c • R.unit t :=
  rfl

/-- The same coordinate equivalence with the carrier of the represented
poset space exposed in its statement. -/
noncomputable def representedProjectiveCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    (R.representableData.obj (R.projective t)).carrier ≃ₗ[k] k := by
  change (S.factorObject K D.source ⟶
    S.factorObject K (R.label t)) ≃ₗ[k] k
  exact R.unitCoordinateEquiv t

@[simp]
theorem representedProjectiveCoordinateEquiv_symm_apply
    (R : S.PrimitiveProjectivePosetData D T) (t : T) (c : k) :
    (R.representedProjectiveCoordinateEquiv t).symm c = c • R.unit t :=
  rfl

/-- The represented image of `P_s` is the one-dimensional poset space on
the principal filter generated by `s`. -/
noncomputable def projectiveObjIsoLine
    (R : S.PrimitiveProjectivePosetData D T) (s : T) :
    R.representableData.obj (R.projective s) ≅
      PosetSpace.line k T (Set.Ici s) (isUpperSet_Ici s) := by
  classical
  exact {
  hom :=
    { linear := R.representedProjectiveCoordinateEquiv s
      map_subspace := by
        intro t x hx
        by_cases hst : s ≤ t
        · change R.representedProjectiveCoordinateEquiv s x ∈
            if t ∈ Set.Ici s then (⊤ : Submodule k k) else ⊥
          rw [if_pos (show t ∈ Set.Ici s from hst)]
          exact Submodule.mem_top
        · obtain ⟨f, hfRange⟩ := hx
          have hf := R.eq_zero_of_projectiveHom_of_not_le hst f
          have hxzero : x = 0 := by
            rw [← hfRange, hf]
            exact (R.representableData.precomposition t
              (R.projective s)).map_zero
          rw [hxzero]
          exact (R.representedProjectiveCoordinateEquiv s).map_zero ▸
            Submodule.zero_mem _ }
  inv :=
    { linear := (R.representedProjectiveCoordinateEquiv s).symm
      map_subspace := by
        intro t c hc
        by_cases hst : s ≤ t
        · refine ⟨c • R.incidenceMap hst, ?_⟩
          change R.unit t ≫ (c • R.incidenceMap hst) =
            (R.representedProjectiveCoordinateEquiv s).symm c
          rw [Linear.comp_smul, R.unit_comp_incidenceMap hst,
            R.representedProjectiveCoordinateEquiv_symm_apply]
        · have hc0 : c = 0 := by
            change c ∈ if t ∈ Set.Ici s then
              (⊤ : Submodule k k) else ⊥ at hc
            rw [if_neg (show t ∉ Set.Ici s from hst)] at hc
            change c = 0 at hc
            exact hc
          subst c
          refine ⟨0, ?_⟩
          exact (R.representableData.precomposition t
            (R.projective s)).map_zero |>.trans
              ((R.representedProjectiveCoordinateEquiv s).symm.map_zero).symm }
  hom_inv_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedProjectiveCoordinateEquiv s).symm_apply_apply x
  inv_hom_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedProjectiveCoordinateEquiv s).apply_symm_apply x }

/-- The distinguished source projective is different from every projective
indexed by `T`. -/
theorem sourceProjectiveLabel_ne_projective
    (R : S.PrimitiveProjectivePosetData D T) (t : T) :
    D.sourceProjectiveLabel ≠ R.projectiveEquiv.symm (some t) := by
  intro h
  have h' := congrArg R.projectiveEquiv h
  simpa [R.source_eq_none] using h'

/-- Directedness rules out a morphism from a non-root projective back to the
distinguished source. -/
theorem eq_zero_of_projectiveHom_to_source
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) (t : T)
    (f : R.projective t ⟶ R.representableData.source) :
    f = 0 := by
  by_contra hf
  have hlabel : R.label t = D.source :=
    HasAcyclicNonzeroNonisomorphisms.factorObject_label_eq_of_two_way
      (S := S) H K (R.label t) D.source f hf
        (R.unit t) (R.unit_ne_zero t)
  apply R.sourceProjectiveLabel_ne_projective t
  exact Subtype.ext hlabel.symm

/-- Scalar multiplication of the identity of the distinguished source. -/
def sourceIdScalarLinearMap
    (R : S.PrimitiveProjectivePosetData D T) :
    k →ₗ[k] (R.representableData.source ⟶ R.representableData.source) where
  toFun c := c • CategoryStruct.id R.representableData.source
  map_add' c d := add_smul c d _
  map_smul' c d := by
    change (c * d) • CategoryStruct.id R.representableData.source =
      c • d • CategoryStruct.id R.representableData.source
    rw [smul_smul]

/-- The identity gives a coordinate on the one-dimensional represented Hom
space of the distinguished source. -/
noncomputable def sourceCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T) :
    (R.representableData.source ⟶ R.representableData.source) ≃ₗ[k] k := by
  have hfinrank : Module.finrank k
      (R.representableData.source ⟶ R.representableData.source) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D D.source).trans
      (R.projective_multiplicity_eq_one D.sourceProjectiveLabel)
  have hid : (CategoryStruct.id R.representableData.source :
      R.representableData.source ⟶ R.representableData.source) ≠ 0 := by
    intro hzero
    exact S.factorObject_not_isZero K D.source
      ((IsZero.iff_id_eq_zero _).2 hzero)
  exact (LinearEquiv.ofBijective R.sourceIdScalarLinearMap ⟨by
    intro c d hcd
    change c • CategoryStruct.id R.representableData.source =
      d • CategoryStruct.id R.representableData.source at hcd
    have hzero : (c - d) • CategoryStruct.id R.representableData.source = 0 := by
      rw [sub_smul, hcd, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hid),
    fun h ↦ exists_smul_eq_of_finrank_eq_one hfinrank hid h⟩).symm

@[simp]
theorem sourceCoordinateEquiv_symm_apply
    (R : S.PrimitiveProjectivePosetData D T) (c : k) :
    R.sourceCoordinateEquiv.symm c =
      c • CategoryStruct.id R.representableData.source :=
  rfl

/-- The source coordinate with the carrier of its represented poset space
exposed. -/
noncomputable def representedSourceCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T) :
    (R.representableData.obj R.representableData.source).carrier ≃ₗ[k] k := by
  change (R.representableData.source ⟶ R.representableData.source) ≃ₗ[k] k
  exact R.sourceCoordinateEquiv

/-- Restricted Yoneda sends the distinguished source to the line with empty
support. -/
noncomputable def sourceObjIsoEmptyLine
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    R.representableData.obj R.representableData.source ≅
      PosetSpace.line k T ∅ isUpperSet_empty := by
  classical
  exact {
  hom :=
    { linear := R.representedSourceCoordinateEquiv
      map_subspace := by
        intro t x hx
        obtain ⟨f, rfl⟩ := hx
        have hzero : R.representableData.precomposition t
            R.representableData.source f = 0 := by
          rw [R.eq_zero_of_projectiveHom_to_source H t f]
          exact (R.representableData.precomposition t
            R.representableData.source).map_zero
        rw [hzero]
        exact R.representedSourceCoordinateEquiv.map_zero ▸
          Submodule.zero_mem _ }
  inv :=
    { linear := R.representedSourceCoordinateEquiv.symm
      map_subspace := by
        intro t c hc
        have hc0 : c = 0 := by
          rw [PosetSpace.line_subspace_of_not_mem k T
            (∅ : Set T) isUpperSet_empty t (by simp)] at hc
          exact hc
        subst c
        refine ⟨0, ?_⟩
        exact (R.representableData.precomposition t
          R.representableData.source).map_zero |>.trans
            (R.representedSourceCoordinateEquiv.symm.map_zero).symm }
  hom_inv_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact R.representedSourceCoordinateEquiv.symm_apply_apply x
  inv_hom_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact R.representedSourceCoordinateEquiv.apply_symm_apply x }

/-- A chosen nonzero element of the one-dimensional represented Hom space of
the distinguished sink. -/
noncomputable def sinkUnit
    (R : S.PrimitiveProjectivePosetData D T) :
    R.representableData.source ⟶ S.factorObject K D.sink :=
  Classical.choose
    (PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero
      (S := S) D D.sink)

theorem sinkUnit_ne_zero
    (R : S.PrimitiveProjectivePosetData D T) : R.sinkUnit ≠ 0 :=
  Classical.choose_spec
    (PrimitiveMultiplicityInput.exists_factorHomFrom_ne_zero
      (S := S) D D.sink)

/-- Scalar multiplication of the chosen source-to-sink map. -/
def sinkUnitScalarLinearMap
    (R : S.PrimitiveProjectivePosetData D T) :
    k →ₗ[k] (R.representableData.source ⟶ S.factorObject K D.sink) where
  toFun c := c • R.sinkUnit
  map_add' c d := add_smul c d R.sinkUnit
  map_smul' c d := by
    change (c * d) • R.sinkUnit = c • d • R.sinkUnit
    rw [smul_smul]

/-- A multiplicity-one sink has its represented Hom space canonically
coordinatized by the chosen source-to-sink map. -/
noncomputable def sinkCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1) :
    (R.representableData.source ⟶ S.factorObject K D.sink) ≃ₗ[k] k := by
  have hfinrank : Module.finrank k
      (R.representableData.source ⟶ S.factorObject K D.sink) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D D.sink).trans hsink
  exact (LinearEquiv.ofBijective R.sinkUnitScalarLinearMap ⟨by
    intro c d hcd
    change c • R.sinkUnit = d • R.sinkUnit at hcd
    have hzero : (c - d) • R.sinkUnit = 0 := by
      rw [sub_smul, hcd, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right
      R.sinkUnit_ne_zero),
    fun h ↦ exists_smul_eq_of_finrank_eq_one hfinrank
      R.sinkUnit_ne_zero h⟩).symm

/-- Precomposition from every non-root projective onto a multiplicity-one
sink is surjective. -/
theorem precomposition_surjective_to_sink
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1) (t : T) :
    Function.Surjective
      (R.representableData.precomposition t (S.factorObject K D.sink)) := by
  have hsource : Module.finrank k
      (R.projective t ⟶ S.factorObject K D.sink) = 1 :=
    (PrimitiveMultiplicityInput.factorHomTo_finrank_eq_multiplicity
      (S := S) D (R.label t)).trans
      (R.projective_multiplicity_eq_one
        (R.projectiveEquiv.symm (some t)))
  have htarget : Module.finrank k
      (R.representableData.source ⟶ S.factorObject K D.sink) = 1 :=
    (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
      (S := S) D D.sink).trans hsink
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hsource.trans htarget.symm)).mp
      (R.precomposition_injective t (S.factorObject K D.sink))

/-- The sink coordinate with the represented carrier exposed. -/
noncomputable def representedSinkCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1) :
    (R.representableData.obj (S.factorObject K D.sink)).carrier ≃ₗ[k] k := by
  change (R.representableData.source ⟶ S.factorObject K D.sink) ≃ₗ[k] k
  exact R.sinkCoordinateEquiv hsink

/-- Restricted Yoneda sends a multiplicity-one distinguished sink to the
line with full support. -/
noncomputable def sinkObjIsoFullLine
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1) :
    R.representableData.obj (S.factorObject K D.sink) ≅
      PosetSpace.line k T Set.univ isUpperSet_univ := by
  classical
  exact {
  hom :=
    { linear := R.representedSinkCoordinateEquiv hsink
      map_subspace := by
        intro t x hx
        rw [PosetSpace.line_subspace_of_mem k T
          (Set.univ : Set T) isUpperSet_univ t (Set.mem_univ t)]
        exact Submodule.mem_top }
  inv :=
    { linear := (R.representedSinkCoordinateEquiv hsink).symm
      map_subspace := by
        intro t c hc
        obtain ⟨f, hf⟩ := R.precomposition_surjective_to_sink hsink t
          ((R.representedSinkCoordinateEquiv hsink).symm c)
        exact ⟨f, hf⟩ }
  hom_inv_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedSinkCoordinateEquiv hsink).symm_apply_apply x
  inv_hom_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedSinkCoordinateEquiv hsink).apply_symm_apply x }

/-- The total dimension of the realized selected indecomposable is exactly
the ambient primitive multiplicity `d_X`. -/
theorem finrank_obj_factorObject
    (R : S.PrimitiveProjectivePosetData D T)
    (x : S.SurvivingLabel K) :
    Module.finrank k (R.representableData.obj (S.factorObject K x)) =
      D.multiplicity x.1 := by
  rw [R.representableData.finrank_obj]
  calc
    Module.finrank k
        (S.factorObject K D.source ⟶ S.factorObject K x) =
        Module.finrank k (S.fgObj D.source.1 ⟶ S.fgObj x.1) :=
      (S.factorHomFromLinearEquiv D.noMapsFromKilled x).finrank_eq.symm
    _ = D.multiplicity x.1 := (D.multiplicity_eq_sourceHom x.1).symm

/-- Every surviving selected indecomposable has a nonzero map from the
distinguished source, because its primitive multiplicity is positive. -/
theorem exists_source_hom_ne_zero
    (R : S.PrimitiveProjectivePosetData D T)
    (x : S.SurvivingLabel K) :
    ∃ h : R.representableData.source ⟶ S.factorObject K x, h ≠ 0 := by
  change ∃ h : S.factorObject K D.source ⟶ S.factorObject K x, h ≠ 0
  apply (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp
  change 0 < Module.finrank k
    (S.factorObject K D.source ⟶ S.factorObject K x)
  rw [← (S.factorHomFromLinearEquiv D.noMapsFromKilled x).finrank_eq,
    ← D.multiplicity_eq_sourceHom]
  exact PrimitiveMultiplicityInput.multiplicity_pos (S := S) D x

end PrimitiveProjectivePosetData

namespace PrimitiveDirectedBoundaryData

variable {S} {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The concrete primitive boundary sends its distinguished source to the
empty-support line. -/
noncomputable def sourceObjIsoEmptyLine
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.projectivePosetData.representableData.obj
        B.projectivePosetData.representableData.source ≅
      PosetSpace.line k B.ProjectivePoset ∅ isUpperSet_empty :=
  B.projectivePosetData.sourceObjIsoEmptyLine B.acyclic

/-- The concrete primitive boundary sends its distinguished sink to the
full-support line. -/
noncomputable def sinkObjIsoFullLine
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.projectivePosetData.representableData.obj
        (S.factorObject K D.sink) ≅
      PosetSpace.line k B.ProjectivePoset Set.univ isUpperSet_univ :=
  B.projectivePosetData.sinkObjIsoFullLine
    (B.injective_multiplicity_eq_one D.sinkInjectiveLabel)

/-- The directed boundary package gives the manuscript's exact projective
count `p = |T| + 1`. -/
theorem card_factorProjectiveLabel
    (B : S.PrimitiveDirectedBoundaryData D) :
    Fintype.card (S.FactorProjectiveLabel K) =
      Fintype.card B.ProjectivePoset + 1 :=
  B.projectivePosetData.card_factorProjectiveLabel

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
