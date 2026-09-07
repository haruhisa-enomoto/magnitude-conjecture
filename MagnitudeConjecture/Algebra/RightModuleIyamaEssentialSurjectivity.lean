import MagnitudeConjecture.Algebra.RightModuleIyamaNakayamaSaturation
import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryPresentation

/-!
# Essential surjectivity of the primitive restricted Yoneda functor

Iyama saturation enlarges the lifted image of a represented boundary cover
inside a full-generator representable.  The strict-tau homological estimates
make that saturated image projective, so the additive Auslander equivalence
returns it to a literal factor object.

The boundary idempotent shows that the boundary cover remains surjective after
this replacement.  Its weak-cokernel property then identifies the represented
factor object with the original poset-space subobject.  Consequently the
restricted Yoneda image is closed under subobjects and, using the full-support
envelope, essentially surjective.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.CategoryTheory

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

variable {k T : Type u} [Field k] [PartialOrder T]

theorem BoundarySurjective.of_comp {X Y Z : Obj k T}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : BoundarySurjective f) (hfg : BoundarySurjective (f ≫ g)) :
    BoundarySurjective g := by
  constructor
  · intro z
    obtain ⟨x, hx⟩ := hfg.1 z
    exact ⟨f.linear x, hx⟩
  · intro t
    calc
      Submodule.map g.linear (Y.subspace t) =
          Submodule.map g.linear
            (Submodule.map f.linear (X.subspace t)) := by rw [hf.2 t]
      _ = Submodule.map (f ≫ g).linear (X.subspace t) := by
        rw [comp_linear, Submodule.map_comp]
      _ = Z.subspace t := hfg.2 t

theorem linear_injective_of_mono {X Y : Obj k T} (f : X ⟶ Y)
    [Mono f] : Function.Injective f.linear := by
  intro x y hxy
  let lx : line k T emptySupport emptySupport_isUpperSet ⟶ X :=
    lineMapOfVector emptySupport emptySupport_isUpperSet X x
      (fun _ h ↦ False.elim h)
  let ly : line k T emptySupport emptySupport_isUpperSet ⟶ X :=
    lineMapOfVector emptySupport emptySupport_isUpperSet X y
      (fun _ h ↦ False.elim h)
  have hcomp : lx ≫ f = ly ≫ f := by
    apply Hom.ext
    apply LinearMap.ext
    intro a
    change f.linear (a • x) = f.linear (a • y)
    rw [map_smul, map_smul, hxy]
  have hline : lx = ly := (cancel_mono f).1 hcomp
  have hone := congrArg (fun q ↦ q.linear (1 : k)) hline
  change (1 : k) • x = (1 : k) • y at hone
  simpa only [one_smul] using hone

noncomputable def isoOfBoundarySurjectiveOfInjective
    {X Y : Obj k T} (f : X ⟶ Y)
    (hboundary : BoundarySurjective f)
    (hinjective : Function.Injective f.linear) : X ≅ Y := by
  let e : X ≃ₗ[k] Y :=
    LinearEquiv.ofBijective f.linear ⟨hinjective, hboundary.1⟩
  refine
    { hom := f
      inv :=
        { linear := e.symm
          map_subspace := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro t y hy
    have hy' : y ∈ Submodule.map f.linear (X.subspace t) := by
      rw [hboundary.2 t]
      exact hy
    obtain ⟨x, hx, hxy⟩ := hy'
    have heq : e.symm y = x := by
      apply e.injective
      have happ := e.apply_symm_apply y
      change f.linear (e.symm y) = y at happ
      exact happ.trans hxy.symm
    change e.symm y ∈ X.subspace t
    rw [heq]
    exact hx
  · apply Hom.ext
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  · apply Hom.ext
    apply LinearMap.ext
    intro y
    exact e.apply_symm_apply y

end MagnitudeConjecture.PosetSpace

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

theorem exists_factorObject_representing_saturatedSubobjectImage_unconditional
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    ∃ Z : S.FactorCategory K,
      Nonempty
        ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj Z ≅
          ModuleCat.of (S.factorAuslanderRing K)
            (R.saturatedSubobjectImage H m)) :=
  R.exists_factorObject_representing_saturatedSubobjectImage H m
    (R.saturatedSubobjectAmbientQuotient_projectiveDimensionLE_one H m)

noncomputable def saturatedFactorObject
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) : S.FactorCategory K :=
  Classical.choose
    (R.exists_factorObject_representing_saturatedSubobjectImage_unconditional H m)

noncomputable def saturatedFactorObjectIso
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    (preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj
        (R.saturatedFactorObject H m) ≅
      ModuleCat.of (S.factorAuslanderRing K)
        (R.saturatedSubobjectImage H m) :=
  Classical.choice
    (Classical.choose_spec
      (R.exists_factorObject_representing_saturatedSubobjectImage_unconditional H m))

def liftedSubobjectAuslanderToSaturation
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    (S.factorAdditiveGenerator K ⟶ R.boundaryCoverObject Y) →ₗ[
      S.factorAuslanderRing K]
      R.saturatedSubobjectImage H m :=
  (R.liftedSubobjectAuslanderMap H m).codRestrict
    (R.saturatedSubobjectImage H m)
    (fun a ↦ R.liftedSubobjectImage_le_saturatedSubobjectImage H m
      ⟨a, rfl⟩)

noncomputable def saturatedBoundaryCoverFactor
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.boundaryCoverObject Y ⟶ R.saturatedFactorObject H m :=
  Classical.choose
    (MagnitudeConjecture.CategoryTheory.exists_hom_of_moduleHom_of_finiteAddSource
      (S.factorAdditiveGenerator K)
      (S.factorAdditiveGenerator_isFiniteAddGenerator K
        (R.boundaryCoverObject Y)).some
      (ModuleCat.ofHom (R.liftedSubobjectAuslanderToSaturation H m) ≫
        (R.saturatedFactorObjectIso H m).inv))

theorem map_saturatedBoundaryCoverFactor
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    (preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
        (R.saturatedBoundaryCoverFactor H m) =
      ModuleCat.ofHom (R.liftedSubobjectAuslanderToSaturation H m) ≫
        (R.saturatedFactorObjectIso H m).inv :=
  Classical.choose_spec
    (MagnitudeConjecture.CategoryTheory.exists_hom_of_moduleHom_of_finiteAddSource
      (S.factorAdditiveGenerator K)
      (S.factorAdditiveGenerator_isFiniteAddGenerator K
        (R.boundaryCoverObject Y)).some
      (ModuleCat.ofHom (R.liftedSubobjectAuslanderToSaturation H m) ≫
        (R.saturatedFactorObjectIso H m).inv))

noncomputable def saturatedFactorInclusion
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.saturatedFactorObject H m ⟶ X :=
  Classical.choose
    (MagnitudeConjecture.CategoryTheory.exists_hom_of_moduleHom_of_finiteAddSource
      (S.factorAdditiveGenerator K)
      (S.factorAdditiveGenerator_isFiniteAddGenerator K
        (R.saturatedFactorObject H m)).some
      ((R.saturatedFactorObjectIso H m).hom ≫
        ModuleCat.ofHom (R.saturatedSubobjectImage H m).subtype))

theorem map_saturatedFactorInclusion
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    (preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
        (R.saturatedFactorInclusion H m) =
      (R.saturatedFactorObjectIso H m).hom ≫
        ModuleCat.ofHom (R.saturatedSubobjectImage H m).subtype :=
  Classical.choose_spec
    (MagnitudeConjecture.CategoryTheory.exists_hom_of_moduleHom_of_finiteAddSource
      (S.factorAdditiveGenerator K)
      (S.factorAdditiveGenerator_isFiniteAddGenerator K
        (R.saturatedFactorObject H m)).some
      ((R.saturatedFactorObjectIso H m).hom ≫
        ModuleCat.ofHom (R.saturatedSubobjectImage H m).subtype))

theorem saturatedBoundaryCoverFactor_comp_inclusion
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.saturatedBoundaryCoverFactor H m ≫
        R.saturatedFactorInclusion H m =
      R.liftedSubobjectCoverMap H m := by
  apply D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
  intro h
  change S.factorObject K D.source ⟶ R.boundaryCoverObject Y at h
  change h ≫ (R.saturatedBoundaryCoverFactor H m ≫
      R.saturatedFactorInclusion H m) =
    h ≫ R.liftedSubobjectCoverMap H m
  let F : S.SurvivingLabel K → S.FactorCategory K :=
    fun x ↦ S.factorObject K x
  let π : S.factorAdditiveGenerator K ⟶ S.factorObject K D.source :=
    biproduct.π F D.source
  let ι : S.factorObject K D.source ⟶ S.factorAdditiveGenerator K :=
    biproduct.ι F D.source
  let a : S.factorAdditiveGenerator K ⟶ R.boundaryCoverObject Y := π ≫ h
  have hp := congrArg
    (fun q ↦ q.hom a) (R.map_saturatedBoundaryCoverFactor H m)
  have hz := congrArg
    (fun q ↦ q.hom (a ≫ R.saturatedBoundaryCoverFactor H m))
    (R.map_saturatedFactorInclusion H m)
  have ha :
      (a ≫ R.saturatedBoundaryCoverFactor H m) ≫
          R.saturatedFactorInclusion H m =
        a ≫ R.liftedSubobjectCoverMap H m := by
    have hp' :
        a ≫ R.saturatedBoundaryCoverFactor H m =
          (R.saturatedFactorObjectIso H m).inv.hom
            (R.liftedSubobjectAuslanderToSaturation H m a) := hp
    have hz' :
        (a ≫ R.saturatedBoundaryCoverFactor H m) ≫
            R.saturatedFactorInclusion H m =
          ((R.saturatedFactorObjectIso H m).hom.hom
            (a ≫ R.saturatedBoundaryCoverFactor H m)).1 := hz
    rw [hz', hp']
    simp only [Iso.inv_hom_id_apply]
    rfl
  have hιπ : ι ≫ π = 𝟙 (S.factorObject K D.source) := by
    exact biproduct.ι_π_self F D.source
  have hι := congrArg (fun q ↦ ι ≫ q) ha
  simpa only [a, ← Category.assoc, hιπ, Category.id_comp] using hι

theorem saturatedFactorInclusion_mono
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Mono (R.saturatedFactorInclusion H m) := by
  constructor
  intro W f g hfg
  apply D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
  intro h
  change S.factorObject K D.source ⟶ W at h
  change h ≫ f = h ≫ g
  let F : S.SurvivingLabel K → S.FactorCategory K :=
    fun x ↦ S.factorObject K x
  let π : S.factorAdditiveGenerator K ⟶ S.factorObject K D.source :=
    biproduct.π F D.source
  let ι : S.factorObject K D.source ⟶ S.factorAdditiveGenerator K :=
    biproduct.ι F D.source
  let a : S.factorAdditiveGenerator K ⟶ W := π ≫ h
  have happ := congrArg (fun q : W ⟶ X ↦ a ≫ q) hfg
  have hz' (b : S.factorAdditiveGenerator K ⟶
      R.saturatedFactorObject H m) :
      b ≫ R.saturatedFactorInclusion H m =
        ((R.saturatedFactorObjectIso H m).hom.hom b).1 :=
    congrArg (fun q ↦ q.hom b)
      (R.map_saturatedFactorInclusion H m)
  have hsub :
      (R.saturatedFactorObjectIso H m).hom.hom (a ≫ f) =
        (R.saturatedFactorObjectIso H m).hom.hom (a ≫ g) := by
    apply Subtype.ext
    rw [← hz' (a ≫ f), ← hz' (a ≫ g)]
    simpa only [Category.assoc] using happ
  have ha' : a ≫ f = a ≫ g :=
    (ModuleCat.mono_iff_injective
      (R.saturatedFactorObjectIso H m).hom).1 inferInstance hsub
  have hιπ : ι ≫ π = 𝟙 (S.factorObject K D.source) := by
    exact biproduct.ι_π_self F D.source
  have hι := congrArg (fun q ↦ ι ≫ q) ha'
  simpa only [a, ← Category.assoc, hιπ, Category.id_comp] using hι

theorem saturatedBoundaryCoverFactor_postcomposition_surjective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Function.Surjective
      (fun a : S.factorProjectiveGenerator K ⟶ R.boundaryCoverObject Y ↦
        a ≫ R.saturatedBoundaryCoverFactor H m) := by
  intro b
  let U := S.factorProjectiveGenerator K
  let E := R.saturatedFactorObjectIso H m
  let Q := S.factorProjectiveGeneratorRetract K
  let x : S.factorAdditiveGenerator K ⟶
      R.saturatedFactorObject H m := Q.r ≫ b
  let y : R.saturatedSubobjectImage H m := E.hom.hom x
  have hxfixed : S.factorBoundaryIdempotent K • x = x := by
    change (Q.r ≫ Q.i) ≫ x = x
    dsimp only [x]
    rw [Category.assoc Q.r Q.i (Q.r ≫ b),
      ← Category.assoc Q.i Q.r b, Q.retract, Category.id_comp]
  have hyfixed : S.factorBoundaryIdempotent K • y.1 = y.1 := by
    have hyfixed' : S.factorBoundaryIdempotent K • y = y := by
      calc
        S.factorBoundaryIdempotent K • y =
            E.hom.hom (S.factorBoundaryIdempotent K • x) := by
              exact (E.hom.hom.map_smul _ _).symm
        _ = E.hom.hom x := congrArg E.hom.hom hxfixed
        _ = y := rfl
    exact congrArg Subtype.val hyfixed'
  have hquotient :=
    R.boundaryIdempotent_smul_mkQ_eq_zero_of_mem_saturatedSubobjectImage
      H m y.2
  have hmkQ : (R.liftedSubobjectImage H m).mkQ y.1 = 0 := by
    calc
      (R.liftedSubobjectImage H m).mkQ y.1 =
          (R.liftedSubobjectImage H m).mkQ
            (S.factorBoundaryIdempotent K • y.1) := by rw [hyfixed]
      _ = S.factorBoundaryIdempotent K •
          (R.liftedSubobjectImage H m).mkQ y.1 := by
            rw [map_smul]
      _ = 0 := hquotient
  have hyL : y.1 ∈ R.liftedSubobjectImage H m := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hmkQ
  obtain ⟨a, ha⟩ := hyL
  let c : U ⟶ R.boundaryCoverObject Y := Q.i ≫ a
  refine ⟨c, ?_⟩
  have hp := congrArg (fun q ↦ q.hom a)
    (R.map_saturatedBoundaryCoverFactor H m)
  have hto : R.liftedSubobjectAuslanderToSaturation H m a = y := by
    apply Subtype.ext
    exact ha
  have hap : a ≫ R.saturatedBoundaryCoverFactor H m = x := by
    have hp' : a ≫ R.saturatedBoundaryCoverFactor H m =
        E.inv.hom (R.liftedSubobjectAuslanderToSaturation H m a) := hp
    rw [hp', hto]
    exact E.hom_inv_id_apply x
  calc
    c ≫ R.saturatedBoundaryCoverFactor H m =
        Q.i ≫ (a ≫ R.saturatedBoundaryCoverFactor H m) := by
          exact Category.assoc _ _ _
    _ = Q.i ≫ x := by rw [hap]
    _ = Q.i ≫ (Q.r ≫ b) := by rfl
    _ = (Q.i ≫ Q.r) ≫ b := (Category.assoc _ _ _).symm
    _ = b := by rw [Q.retract, Category.id_comp]

omit [IsAlgClosed k] in
theorem representableData_map_boundarySurjective_of_projectiveGenerator
    (R : S.PrimitiveProjectivePosetData D T)
    {B Z : S.FactorCategory K} (p : B ⟶ Z)
    (hp : Function.Surjective
      (fun a : S.factorProjectiveGenerator K ⟶ B ↦ a ≫ p)) :
    PosetSpace.BoundarySurjective (R.representableData.map p) := by
  let F : S.FactorProjectiveLabel K → S.FactorCategory K :=
    fun q ↦ S.factorObject K q.1
  constructor
  · intro h
    change S.factorObject K D.source ⟶ Z at h
    let π : S.factorProjectiveGenerator K ⟶ S.factorObject K D.source :=
      biproduct.π F D.sourceProjectiveLabel
    let ι : S.factorObject K D.source ⟶ S.factorProjectiveGenerator K :=
      biproduct.ι F D.sourceProjectiveLabel
    obtain ⟨a, ha⟩ := hp (π ≫ h)
    refine ⟨ι ≫ a, ?_⟩
    change (ι ≫ a) ≫ p = h
    have hιπ : ι ≫ π = 𝟙 (S.factorObject K D.source) := by
      exact biproduct.ι_π_self F D.sourceProjectiveLabel
    have ha' : a ≫ p = π ≫ h := ha
    calc
      (ι ≫ a) ≫ p = ι ≫ (a ≫ p) := Category.assoc _ _ _
      _ = ι ≫ (π ≫ h) := by rw [ha']
      _ = (ι ≫ π) ≫ h := (Category.assoc _ _ _).symm
      _ = h := by rw [hιπ, Category.id_comp]
  · intro t
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (R.representableData.map p).map_subspace t x hx
    · intro y hy
      obtain ⟨h, rfl⟩ := hy
      change R.projective t ⟶ Z at h
      let pt : S.FactorProjectiveLabel K :=
        R.projectiveEquiv.symm (some t)
      let π : S.factorProjectiveGenerator K ⟶ R.projective t :=
        biproduct.π F pt
      let ι : R.projective t ⟶ S.factorProjectiveGenerator K :=
        biproduct.ι F pt
      obtain ⟨a, ha⟩ := hp (π ≫ h)
      refine ⟨(R.unit t ≫ ι) ≫ a, ?_, ?_⟩
      · refine ⟨ι ≫ a, ?_⟩
        change R.unit t ≫ (ι ≫ a) = (R.unit t ≫ ι) ≫ a
        exact (Category.assoc _ _ _).symm
      · change ((R.unit t ≫ ι) ≫ a) ≫ p = R.unit t ≫ h
        have hιπ : ι ≫ π = 𝟙 (R.projective t) := by
          exact biproduct.ι_π_self F pt
        have ha' : a ≫ p = π ≫ h := ha
        calc
          ((R.unit t ≫ ι) ≫ a) ≫ p =
              (R.unit t ≫ ι) ≫ (a ≫ p) := Category.assoc _ _ _
          _ = (R.unit t ≫ ι) ≫ (π ≫ h) := by rw [ha']
          _ = ((R.unit t ≫ ι) ≫ π) ≫ h :=
                (Category.assoc _ _ _).symm
          _ = (R.unit t ≫ (ι ≫ π)) ≫ h :=
                congrArg (fun q ↦ q ≫ h) (Category.assoc _ _ _)
          _ = (R.unit t ≫ 𝟙 (R.projective t)) ≫ h := by rw [hιπ]
          _ = R.unit t ≫ h := by rw [Category.comp_id]

theorem saturatedBoundaryCoverFactor_boundarySurjective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    PosetSpace.BoundarySurjective
      (R.representableData.map (R.saturatedBoundaryCoverFactor H m)) :=
  R.representableData_map_boundarySurjective_of_projectiveGenerator
    (R.saturatedBoundaryCoverFactor H m)
    (R.saturatedBoundaryCoverFactor_postcomposition_surjective H m)

theorem liftedBoundaryRelationMap_comp_saturatedBoundaryCoverFactor
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.liftedBoundaryRelationMap H Y ≫
      R.saturatedBoundaryCoverFactor H m = 0 := by
  letI : Mono (R.saturatedFactorInclusion H m) :=
    R.saturatedFactorInclusion_mono H m
  apply (cancel_mono (R.saturatedFactorInclusion H m)).1
  rw [Category.assoc, R.saturatedBoundaryCoverFactor_comp_inclusion H m]
  have hzero : R.liftedBoundaryRelationMap H Y ≫
      R.liftedSubobjectCoverMap H m = 0 := by
    apply R.representable_faithful.map_injective
    rw [Functor.map_comp]
    change R.representableData.map
          (R.liftedBoundaryRelationMap H Y) ≫
        R.representableData.map (R.liftedSubobjectCoverMap H m) =
      R.representableData.map 0
    rw [
      R.map_liftedBoundaryRelationMap H Y,
      R.map_liftedSubobjectCoverMap H m]
    rw [← Category.assoc,
      R.representedBoundaryRelationMap_comp H Y, zero_comp]
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    change 0 = x ≫ 0
    exact comp_zero.symm
  rw [hzero, zero_comp]

theorem map_liftedBoundaryRelationMap_comp_saturatedBoundaryCoverFactor
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.representableData.map (R.liftedBoundaryRelationMap H Y) ≫
      R.representableData.map (R.saturatedBoundaryCoverFactor H m) = 0 := by
  change R.representableData.functor.map
        (R.liftedBoundaryRelationMap H Y) ≫
      R.representableData.functor.map
        (R.saturatedBoundaryCoverFactor H m) = 0
  rw [← Functor.map_comp,
    R.liftedBoundaryRelationMap_comp_saturatedBoundaryCoverFactor H m]
  apply PosetSpace.Hom.ext
  apply LinearMap.ext
  intro x
  change x ≫ 0 = 0
  exact comp_zero

noncomputable def saturatedRealizationMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Y ⟶ R.representableData.obj (R.saturatedFactorObject H m) :=
  Classical.choose
    (R.representedBoundaryCoverMap_weakCokernel_lifted H Y
      (R.representableData.map (R.saturatedBoundaryCoverFactor H m))
      (R.map_liftedBoundaryRelationMap_comp_saturatedBoundaryCoverFactor H m))

theorem representedBoundaryCoverMap_comp_saturatedRealizationMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.representedBoundaryCoverMap H Y ≫ R.saturatedRealizationMap H m =
      R.representableData.map (R.saturatedBoundaryCoverFactor H m) :=
  Classical.choose_spec
    (R.representedBoundaryCoverMap_weakCokernel_lifted H Y
      (R.representableData.map (R.saturatedBoundaryCoverFactor H m))
      (R.map_liftedBoundaryRelationMap_comp_saturatedBoundaryCoverFactor H m))

theorem saturatedRealizationMap_boundarySurjective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    PosetSpace.BoundarySurjective (R.saturatedRealizationMap H m) := by
  apply PosetSpace.BoundarySurjective.of_comp
    (R.representedBoundaryCoverMap_boundarySurjective H Y)
  rw [R.representedBoundaryCoverMap_comp_saturatedRealizationMap H m]
  exact R.saturatedBoundaryCoverFactor_boundarySurjective H m

theorem saturatedRealizationMap_comp_inclusion
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.saturatedRealizationMap H m ≫
      R.representableData.map (R.saturatedFactorInclusion H m) = m := by
  let q := R.representedBoundaryCoverMap H Y
  have hqsurj := R.representedBoundaryCoverMap_boundarySurjective H Y
  letI : Epi q := PosetSpace.epi_of_linear_surjective q hqsurj.1
  apply (cancel_epi q).1
  dsimp only [q]
  rw [← Category.assoc,
    R.representedBoundaryCoverMap_comp_saturatedRealizationMap H m]
  change
    R.representableData.functor.map (R.saturatedBoundaryCoverFactor H m) ≫
        R.representableData.functor.map
          (R.saturatedFactorInclusion H m) =
      R.representedBoundaryCoverMap H Y ≫ m
  rw [← Functor.map_comp,
    R.saturatedBoundaryCoverFactor_comp_inclusion H m]
  simpa only [PosetSpace.RepresentableData.functor_map,
    PosetSpace.RepresentableData.functor_obj] using
      R.map_liftedSubobjectCoverMap H m

noncomputable def saturatedRealizationIso
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) [Mono m] :
    Y ≅ R.representableData.obj (R.saturatedFactorObject H m) := by
  let s := R.saturatedRealizationMap H m
  let z := R.representableData.map (R.saturatedFactorInclusion H m)
  have hscomp : s ≫ z = m := R.saturatedRealizationMap_comp_inclusion H m
  letI : Mono s := mono_of_mono_fac hscomp
  exact PosetSpace.isoOfBoundarySurjectiveOfInjective s
    (R.saturatedRealizationMap_boundarySurjective H m)
    (PosetSpace.linear_injective_of_mono s)

theorem representable_closedUnderSubobjects
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    R.representableData.EssentialImageClosedUnderSubobjects := by
  intro Y X m hm
  letI : Mono m := hm
  exact ⟨R.saturatedFactorObject H m,
    ⟨(R.saturatedRealizationIso H m).symm⟩⟩

theorem representable_essentiallySurjective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hsink : D.multiplicity D.sink.1 = 1) :
    ∀ Y : PosetSpace.Obj k T,
      ∃ X : S.FactorCategory K,
        Nonempty (R.representableData.obj X ≅ Y) :=
  R.representable_essSurj_of_closedUnderSubobjects
    hsink
    (R.representable_closedUnderSubobjects H)

end PrimitiveProjectivePosetData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
