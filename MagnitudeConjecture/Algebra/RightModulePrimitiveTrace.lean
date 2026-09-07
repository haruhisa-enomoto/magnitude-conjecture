import MagnitudeConjecture.Algebra.RightModuleFactorStrict
import QuotientSubmoduleEquidistribution.RepresentationTheory.Trace

/-!
# Trace criteria for primitive-deletion factors

The frozen manuscript proves faithfulness of the distinguished factor
representable by a trace argument: a morphism killed by every map from the
projective cover factors through the killed module subcategory.  This file
isolates that ambient factorization statement and proves that it supplies the
faithfulness hypotheses used by `PrimitiveFactorInput`.  The dual statement
uses the distinguished injective sink.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The paper's source-trace factorization statement: an ambient morphism
annihilated after precomposition by every map from the distinguished source
factors through the killed additive subcategory. -/
def SourceTraceFactorization
    (K : Set (Fin S.n)) (p : S.SurvivingLabel K) : Prop :=
  ∀ {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y),
    (∀ a : S.ambientAddPoint p.1 ⟶ X, a ≫ f = 0) →
      S.FactorsThroughSelected K f.hom

/-- The dual sink-reject factorization statement: an ambient morphism
annihilated after postcomposition by every map to the distinguished sink
factors through the killed additive subcategory. -/
def SinkRejectFactorization
    (K : Set (Fin S.n)) (i : S.SurvivingLabel K) : Prop :=
  ∀ {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y),
    (∀ a : Y ⟶ S.ambientAddPoint i.1, f ≫ a = 0) →
      S.FactorsThroughSelected K f.hom

/-- The singleton trace of the distinguished source in a finitely generated
ambient module. -/
abbrev sourceTraceSubmodule
    (p : Fin S.n) (X : RightModule.FinitelyGeneratedCategory A) :
    Submodule Aᵐᵒᵖ X :=
  S.almostSplitSkeleton.trace {p} X

/-- The ambient module quotient by the singleton source trace. -/
def sourceTraceQuotient
    (p : Fin S.n) (X : RightModule.FinitelyGeneratedCategory A) :
    RightModule.FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ (X ⧸ S.sourceTraceSubmodule p X)

/-- The canonical map to the quotient by the singleton source trace. -/
def sourceTraceQuotientMap
    (p : Fin S.n) (X : RightModule.FinitelyGeneratedCategory A) :
    X ⟶ S.sourceTraceQuotient p X :=
  FGModuleCat.ofHom (Submodule.mkQ (S.sourceTraceSubmodule p X))

/-- The singleton reject of the distinguished sink, regarded as a finitely
generated ambient submodule. -/
def sinkRejectObject
    (i : Fin S.n) (Y : RightModule.FinitelyGeneratedCategory A) :
    RightModule.FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ (S.almostSplitSkeleton.reject {i} Y)

/-- The canonical inclusion of the singleton sink reject. -/
def sinkRejectInclusion
    (i : Fin S.n) (Y : RightModule.FinitelyGeneratedCategory A) :
    S.sinkRejectObject i Y ⟶ Y :=
  FGModuleCat.ofHom (S.almostSplitSkeleton.reject {i} Y).subtype

/-- If every map from `p` becomes zero after postcomposition by `f`, then
the singleton source trace is contained in the kernel of `f`. -/
theorem sourceTraceSubmodule_le_ker
    (p : Fin S.n) {X Y : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y)
    (hzero : ∀ a : S.almostSplitSkeleton.obj p ⟶ X, a ≫ f = 0) :
    S.sourceTraceSubmodule p X ≤ LinearMap.ker f.hom.hom := by
  rw [sourceTraceSubmodule,
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.trace]
  apply iSup_le
  intro a
  rw [LinearMap.range_le_ker_iff]
  have hcomp : a.map ≫ f = 0 := by
    apply biproduct.hom_ext'
    intro t
    have ht : a.label t = p := Set.mem_singleton_iff.mp (a.mem t)
    let e : S.almostSplitSkeleton.obj p ≅
        S.almostSplitSkeleton.obj (a.label t) :=
      eqToIso (congrArg S.almostSplitSkeleton.obj ht.symm)
    rw [comp_zero]
    apply (cancel_epi e.hom).1
    have h := hzero (e.hom ≫
        biproduct.ι
          (fun t : a.index ↦ S.fgObj (a.label t)) t ≫ a.map)
    change
      e.hom ≫
          biproduct.ι
            (fun t : a.index ↦
              S.almostSplitSkeleton.obj (a.label t)) t ≫
            a.map ≫ f = 0 at h
    rw [comp_zero]
    simpa only [Category.assoc] using h
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcomp
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun q ↦ q x) hlinear
  change (f.hom.hom.comp a.map.hom.hom) x = 0 at hx
  exact hx

/-- If every map to `i` becomes zero after precomposition by `f`, then the
range of `f` lies in the singleton sink reject. -/
theorem range_le_sinkReject
    (i : Fin S.n) {X Y : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y)
    (hzero : ∀ a : Y ⟶ S.almostSplitSkeleton.obj i, f ≫ a = 0) :
    LinearMap.range f.hom.hom ≤
      S.almostSplitSkeleton.reject {i} Y := by
  rw [QuotientSubmoduleEquidistribution.IndecomposableSkeleton.reject]
  apply le_iInf
  intro a
  rw [LinearMap.range_le_ker_iff]
  have hcomp : f ≫ a.map = 0 := by
    apply biproduct.hom_ext
    intro t
    have ht : a.label t = i := Set.mem_singleton_iff.mp (a.mem t)
    let e : S.almostSplitSkeleton.obj (a.label t) ≅
        S.almostSplitSkeleton.obj i :=
      eqToIso (congrArg S.almostSplitSkeleton.obj ht)
    simp only [Category.assoc, zero_comp]
    apply (cancel_mono e.hom).1
    have h := hzero (a.map ≫
        biproduct.π
          (fun t : a.index ↦ S.fgObj (a.label t)) t ≫ e.hom)
    change
      f ≫ a.map ≫
          biproduct.π
            (fun t : a.index ↦
              S.almostSplitSkeleton.obj (a.label t)) t ≫
            e.hom = 0 at h
    rw [zero_comp]
    simpa only [Category.assoc] using h
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcomp
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun q ↦ q x) hlinear
  change (a.map.hom.hom.comp f.hom.hom) x = 0 at hx
  exact hx

/-- Every singleton source-trace quotient belongs to the killed additive
subcategory.  This is the module-theoretic content needed in the paper's
trace proof. -/
def SourceTraceQuotientsKilled
    (K : Set (Fin S.n)) (p : S.SurvivingLabel K) : Prop :=
  ∀ X : RightModule.FinitelyGeneratedCategory A,
    S.almostSplitSkeleton.InAdd K (S.sourceTraceQuotient p.1 X)

/-- Every singleton sink reject belongs to the killed additive subcategory.
This is the dual module-theoretic content of the paper's trace proof. -/
def SinkRejectsKilled
    (K : Set (Fin S.n)) (i : S.SurvivingLabel K) : Prop :=
  ∀ Y : RightModule.FinitelyGeneratedCategory A,
    S.almostSplitSkeleton.InAdd K (S.sinkRejectObject i.1 Y)

/-- Labels on which the distinguished source representable vanishes. -/
def sourceHomKilledLabels (p : Fin S.n) : Set (Fin S.n) :=
  {x | ∀ f : S.fgObj p ⟶ S.fgObj x, f = 0}

/-- Labels on which the distinguished sink corepresentable vanishes. -/
def sinkHomKilledLabels (i : Fin S.n) : Set (Fin S.n) :=
  {x | ∀ f : S.fgObj x ⟶ S.fgObj i, f = 0}

/-- If a module receives no nonzero map from the distinguished source, all
of its indecomposable summands have source-vanishing labels. -/
theorem inAdd_sourceHomKilledLabels_of_noMaps
    (p : Fin S.n) (M : RightModule.FinitelyGeneratedCategory A)
    (hzero : ∀ f : S.fgObj p ⟶ M, f = 0) :
    S.almostSplitSkeleton.InAdd (S.sourceHomKilledLabels p) M := by
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition (k := k) M
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := label
    mem := ?_
    iso := e }⟩
  intro t f
  let inclusion : S.fgObj (label t) ⟶ M :=
    biproduct.ι (fun j : Fin n ↦ S.fgObj (label j)) t ≫ e.inv
  haveI : Mono inclusion := inferInstance
  apply (cancel_mono inclusion).1
  exact (hzero (f ≫ inclusion)).trans zero_comp.symm

/-- If a module has no nonzero map to the distinguished sink, all of its
indecomposable summands have sink-vanishing labels. -/
theorem inAdd_sinkHomKilledLabels_of_noMaps
    (i : Fin S.n) (M : RightModule.FinitelyGeneratedCategory A)
    (hzero : ∀ f : M ⟶ S.fgObj i, f = 0) :
    S.almostSplitSkeleton.InAdd (S.sinkHomKilledLabels i) M := by
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition (k := k) M
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := label
    mem := ?_
    iso := e }⟩
  intro t f
  let projection : M ⟶ S.fgObj (label t) :=
    e.hom ≫ biproduct.π (fun j : Fin n ↦ S.fgObj (label j)) t
  haveI : Epi projection := inferInstance
  apply (cancel_epi projection).1
  exact (hzero (projection ≫ f)).trans comp_zero.symm

/-- The quotient by the singleton source trace receives no nonzero map from
that source when the source is projective. -/
theorem sourceTraceQuotient_noMaps_of_projective
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (X : RightModule.FinitelyGeneratedCategory A) :
    ∀ f : S.fgObj p ⟶ S.sourceTraceQuotient p X, f = 0 := by
  letI : Projective (S.fgObj p) := hp
  let q : X ⟶ S.sourceTraceQuotient p X :=
    S.sourceTraceQuotientMap p X
  haveI : Epi q :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).2
      (Submodule.mkQ_surjective (S.sourceTraceSubmodule p X))
  intro f
  let lift : S.fgObj p ⟶ X := Projective.factorThru f q
  have hrange : LinearMap.range lift.hom.hom ≤
      S.sourceTraceSubmodule p X :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.range_le_trace_of_mem
      S.almostSplitSkeleton (Set.mem_singleton p) lift
  have hlift : lift ≫ q = 0 := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Submodule.mkQ (S.sourceTraceSubmodule p X)
      (lift.hom.hom x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hrange (LinearMap.mem_range_self lift.hom.hom x)
  rw [← Projective.factorThru_comp f q]
  exact hlift

/-- Projectivity makes every singleton source-trace quotient an object of
the source-Hom-vanishing additive subcategory. -/
theorem sourceTraceQuotientsKilled_of_projective
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    ∀ X : RightModule.FinitelyGeneratedCategory A,
      S.almostSplitSkeleton.InAdd
        (S.sourceHomKilledLabels p) (S.sourceTraceQuotient p X) := by
  intro X
  exact S.inAdd_sourceHomKilledLabels_of_noMaps p _
    (S.sourceTraceQuotient_noMaps_of_projective p hp X)

/-- The singleton sink reject is contained in the kernel of every map to
the distinguished sink. -/
theorem sinkReject_le_ker
    (i : Fin S.n) (Y : RightModule.FinitelyGeneratedCategory A)
    (f : Y ⟶ S.fgObj i) :
    S.almostSplitSkeleton.reject {i} Y ≤ LinearMap.ker f.hom.hom := by
  let a : Fin 1 → Fin S.n := fun _ ↦ i
  let e :
      S.almostSplitSkeleton.sumOver (FintypeCat.of (Fin 1)) a ≅
        S.fgObj i :=
    biproductUniqueIso fun t : Fin 1 ↦ S.fgObj (a t)
  let g : S.almostSplitSkeleton.SelectedMapFrom {i} Y :=
    { index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ Set.mem_singleton i
      map := f ≫ e.inv }
  have hreject :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.reject_le_ker
      S.almostSplitSkeleton g
  intro x hx
  have hxcomp := hreject hx
  rw [LinearMap.mem_ker] at hxcomp ⊢
  have hinj : Function.Injective e.inv.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
      e.inv).1 inferInstance
  apply hinj
  simpa only [map_zero, g, FGModuleCat.hom_hom_comp,
    LinearMap.comp_apply] using hxcomp

/-- The singleton sink reject has no nonzero maps to an injective
distinguished sink. -/
theorem sinkRejectObject_noMaps_of_injective
    (i : Fin S.n) (hi : Injective (S.fgObj i))
    (Y : RightModule.FinitelyGeneratedCategory A) :
    ∀ f : S.sinkRejectObject i Y ⟶ S.fgObj i, f = 0 := by
  letI : Injective (S.fgObj i) := hi
  let inclusion : S.sinkRejectObject i Y ⟶ Y :=
    S.sinkRejectInclusion i Y
  haveI : Mono inclusion :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
      inclusion).2 Subtype.val_injective
  intro f
  let extend : Y ⟶ S.fgObj i := Injective.factorThru f inclusion
  have hker := S.sinkReject_le_ker i Y extend
  have hcomp : inclusion ≫ extend = 0 := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change extend.hom.hom x.1 = 0
    exact (LinearMap.mem_ker.mp (hker x.2))
  rw [← Injective.comp_factorThru f inclusion]
  exact hcomp

/-- Injectivity makes every singleton sink reject an object of the
sink-Hom-vanishing additive subcategory. -/
theorem sinkRejectsKilled_of_injective
    (i : Fin S.n) (hi : Injective (S.fgObj i)) :
    ∀ Y : RightModule.FinitelyGeneratedCategory A,
      S.almostSplitSkeleton.InAdd
        (S.sinkHomKilledLabels i) (S.sinkRejectObject i Y) := by
  intro Y
  exact S.inAdd_sinkHomKilledLabels_of_noMaps i _
    (S.sinkRejectObject_noMaps_of_injective i hi Y)

/-- Killed singleton trace quotients give the source-trace factorization
criterion used to prove quotient faithfulness. -/
theorem sourceTraceFactorization_of_quotientsKilled
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hkilled : S.SourceTraceQuotientsKilled K p) :
    S.SourceTraceFactorization K p := by
  intro X Y f hzero
  let Q := S.sourceTraceQuotient p.1 X.obj
  let q : X.obj ⟶ Q := S.sourceTraceQuotientMap p.1 X.obj
  have hzero' : ∀ a : S.almostSplitSkeleton.obj p.1 ⟶ X.obj,
      a ≫ f.hom = 0 := by
    intro a
    have h := congrArg (fun q ↦ q.hom)
      (hzero (ObjectProperty.homMk a))
    change a ≫ f.hom = 0 at h
    exact h
  let lift : Q ⟶ Y.obj := FGModuleCat.ofHom
    (Submodule.liftQ (S.sourceTraceSubmodule p.1 X.obj)
      f.hom.hom.hom
      (S.sourceTraceSubmodule_le_ker p.1 f.hom hzero'))
  refine ⟨Q, hkilled X.obj, q, lift, ?_⟩
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- Killed singleton sink rejects give the dual reject-factorization
criterion used to prove quotient corepresentable faithfulness. -/
theorem sinkRejectFactorization_of_rejectsKilled
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hkilled : S.SinkRejectsKilled K i) :
    S.SinkRejectFactorization K i := by
  intro X Y f hzero
  let R := S.almostSplitSkeleton.reject {i.1} Y.obj
  let M := S.sinkRejectObject i.1 Y.obj
  have hzero' : ∀ a : Y.obj ⟶ S.almostSplitSkeleton.obj i.1,
      f.hom ≫ a = 0 := by
    intro a
    have h := congrArg (fun q ↦ q.hom)
      (hzero (ObjectProperty.homMk a))
    change f.hom ≫ a = 0 at h
    exact h
  have hrange : LinearMap.range f.hom.hom.hom ≤ R :=
    S.range_le_sinkReject i.1 f.hom hzero'
  let corestrict : X.obj ⟶ M :=
    FGModuleCat.ofHom (f.hom.hom.hom.codRestrict R
      (fun x ↦ hrange (LinearMap.mem_range_self _ x)))
  let inclusion : M ⟶ Y.obj := S.sinkRejectInclusion i.1 Y.obj
  refine ⟨M, hkilled Y.obj, corestrict, inclusion, ?_⟩
  apply FGModuleCat.hom_ext
  rfl

/-- Source-to-killed vanishing upgrades the ambient trace-factorization
criterion to faithfulness of the represented Hom functor on the factor. -/
theorem factorRepresentableFaithful_of_sourceTrace
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (htrace : S.SourceTraceFactorization K p) :
    S.FactorRepresentableFaithful K p := by
  intro X Y f g hfg
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let I := S.factorThroughSelectedIdeal K
  obtain ⟨f', rfl⟩ := (S.factorFunctor K).map_surjective f
  obtain ⟨g', rfl⟩ := (S.factorFunctor K).map_surjective g
  apply CategoryTheory.Quotient.sound
  change S.FactorsThroughSelected K (f'.hom - g'.hom)
  apply htrace (f' - g')
  intro a
  have hmap : (S.factorFunctor K).map (a ≫ (f' - g')) = 0 := by
    rw [Functor.map_comp, Functor.map_sub]
    have h := hfg ((S.factorFunctor K).map a)
    rw [Preadditive.comp_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (a ≫ (f' - g'))).1 hmap
  have hleft : left = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsFromKilled
      hvanish hM left
  apply ObjectProperty.hom_ext
  change a.hom ≫ (f'.hom - g'.hom) = 0
  change left ≫ right = a.hom ≫ (f'.hom - g'.hom) at hfactor
  rw [← hfactor, hleft]
  simp

/-- Killed-to-sink vanishing upgrades the ambient reject-factorization
criterion to faithfulness of the corepresented Hom functor on the factor. -/
theorem factorCorepresentableFaithful_of_sinkReject
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hreject : S.SinkRejectFactorization K i) :
    S.FactorCorepresentableFaithful K i := by
  intro X Y f g hfg
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let I := S.factorThroughSelectedIdeal K
  obtain ⟨f', rfl⟩ := (S.factorFunctor K).map_surjective f
  obtain ⟨g', rfl⟩ := (S.factorFunctor K).map_surjective g
  apply CategoryTheory.Quotient.sound
  change S.FactorsThroughSelected K (f'.hom - g'.hom)
  apply hreject (f' - g')
  intro a
  have hmap : (S.factorFunctor K).map ((f' - g') ≫ a) = 0 := by
    rw [Functor.map_comp, Functor.map_sub]
    have h := hfg ((S.factorFunctor K).map a)
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr h
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff ((f' - g') ≫ a)).1 hmap
  have hright : right = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsToKilled
      hvanish hM right
  apply ObjectProperty.hom_ext
  change (f'.hom - g'.hom) ≫ a.hom = 0
  change left ≫ right = (f'.hom - g'.hom) ≫ a.hom at hfactor
  rw [← hfactor, hright]
  simp

/-- Primitive-factor data phrased with the manuscript's concrete trace
quotients and reject submodules rather than quotient faithfulness
assumptions. -/
structure PrimitiveTraceInput (K : Set (Fin S.n)) where
  source : S.SurvivingLabel K
  sink : S.SurvivingLabel K
  source_projective : Projective (S.fgObj source.1)
  sink_injective : Injective (S.fgObj sink.1)
  killed_iff_sourceHomZero : ∀ x,
    x ∈ K ↔ ∀ f : S.fgObj source.1 ⟶ S.fgObj x, f = 0
  killed_iff_sinkHomZero : ∀ x,
    x ∈ K ↔ ∀ f : S.fgObj x ⟶ S.fgObj sink.1, f = 0
  weight : S.SurvivingLabel K → ℤ
  weight_pos : ∀ x, 0 < weight x
  weight_eq_from : ∀ x,
    weight x =
      MagnitudeConjecture.FiniteTauMatrix.homFromWeight
        (k := k) (S.factorFiniteTauCategoryData K) source x
  weight_eq_to : ∀ x,
    weight x =
      MagnitudeConjecture.FiniteTauMatrix.homToWeight
        (k := k) (S.factorFiniteTauCategoryData K) sink x

/-- The source Hom-vanishing characterization immediately gives the
source-to-killed vanishing used in the factor. -/
theorem PrimitiveTraceInput.noMapsFromKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.NoMapsFromKilled K D.source := by
  intro x hx f
  exact (D.killed_iff_sourceHomZero x).1 hx f

/-- The sink Hom-vanishing characterization immediately gives the
killed-to-sink vanishing used in the factor. -/
theorem PrimitiveTraceInput.noMapsToKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.NoMapsToKilled K D.sink := by
  intro x hx f
  exact (D.killed_iff_sinkHomZero x).1 hx f

/-- Projectivity and the exact source Hom-vanishing characterization put
every singleton trace quotient in the killed additive subcategory. -/
theorem PrimitiveTraceInput.sourceTraceQuotientsKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.SourceTraceQuotientsKilled K D.source := by
  intro X
  apply S.almostSplitSkeleton.inAdd_mono (T := K)
    (fun x hx ↦ (D.killed_iff_sourceHomZero x).2 hx)
  exact S.sourceTraceQuotientsKilled_of_projective
    D.source.1 D.source_projective X

/-- Injectivity and the exact sink Hom-vanishing characterization put every
singleton reject in the killed additive subcategory. -/
theorem PrimitiveTraceInput.sinkRejectsKilled
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.SinkRejectsKilled K D.sink := by
  intro Y
  apply S.almostSplitSkeleton.inAdd_mono (T := K)
    (fun x hx ↦ (D.killed_iff_sinkHomZero x).2 hx)
  exact S.sinkRejectsKilled_of_injective
    D.sink.1 D.sink_injective Y

/-- The concrete killed trace quotients supply the paper's ambient source
factorization statement. -/
theorem PrimitiveTraceInput.sourceTraceFactorization
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.SourceTraceFactorization K D.source :=
  S.sourceTraceFactorization_of_quotientsKilled
    D.sourceTraceQuotientsKilled

/-- The concrete killed-reject field supplies the dual ambient
factorization statement. -/
theorem PrimitiveTraceInput.sinkRejectFactorization
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.SinkRejectFactorization K D.sink :=
  S.sinkRejectFactorization_of_rejectsKilled D.sinkRejectsKilled

/-- The trace-form primitive input supplies the quotient-faithfulness form
used by the strict factor and unit-equation theorems. -/
def PrimitiveTraceInput.toPrimitiveFactorInput
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K) :
    S.PrimitiveFactorInput K where
  source := D.source
  sink := D.sink
  source_projective := D.source_projective
  sink_injective := D.sink_injective
  noMapsFromKilled := D.noMapsFromKilled
  noMapsToKilled := D.noMapsToKilled
  representableFaithful :=
    S.factorRepresentableFaithful_of_sourceTrace
      D.noMapsFromKilled D.sourceTraceFactorization
  corepresentableFaithful :=
    S.factorCorepresentableFaithful_of_sinkReject
      D.noMapsToKilled D.sinkRejectFactorization
  weight := D.weight
  weight_pos := D.weight_pos
  weight_eq_from := D.weight_eq_from
  weight_eq_to := D.weight_eq_to

/-- The manuscript's source trace statement makes all factor right meshes
strict. -/
theorem PrimitiveTraceInput.rightMesh_mono
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K)
    (x : S.SurvivingLabel K) :
    Mono ((S.factorFiniteTauCategoryData K).rightMesh
      ((S.factorFiniteTauCategoryData K).obj x)).f :=
  PrimitiveFactorInput.rightMesh_mono
    (S := S) D.toPrimitiveFactorInput x

/-- The dual sink reject statement makes all factor left meshes strict. -/
theorem PrimitiveTraceInput.leftMesh_epi
    {K : Set (Fin S.n)} (D : S.PrimitiveTraceInput K)
    (x : S.SurvivingLabel K) :
    Epi ((S.factorFiniteTauCategoryData K).leftMesh
      ((S.factorFiniteTauCategoryData K).obj x)).g :=
  PrimitiveFactorInput.leftMesh_epi
    (S := S) D.toPrimitiveFactorInput x

/-- Over an algebraically closed field, trace-form primitive data supplies
the complete Hom--mesh inverse package. -/
theorem PrimitiveTraceInput.homMeshInverseData
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveTraceInput K) :
    MagnitudeConjecture.FiniteTauMatrix.HomMeshInverseData
      (k := k) (S.factorFiniteTauCategoryData K) :=
  D.toPrimitiveFactorInput.homMeshInverseData

/-- Trace-form primitive data satisfies both mesh unit equations. -/
theorem PrimitiveTraceInput.meshUnitEquations
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveTraceInput K) :
    (∀ target,
      MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight
          (S.factorFiniteTauCategoryData K) D.weight target =
        if target = D.source then 1 else 0) ∧
      ∀ source,
        MagnitudeConjecture.FiniteTauMatrix.meshRowWeight
            (S.factorFiniteTauCategoryData K) D.weight source =
          if source = D.sink then 1 else 0 :=
  D.toPrimitiveFactorInput.meshUnitEquations

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
