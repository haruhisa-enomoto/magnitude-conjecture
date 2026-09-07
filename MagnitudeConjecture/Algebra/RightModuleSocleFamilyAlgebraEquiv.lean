import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleFamily

/-!
# Socle families under algebra equivalence

An algebra equivalence transports a complete primitive-projective
presentation label by label.  This file records that transport before
identifying the corresponding embedded socle ideals.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace MagnitudeConjecture

universe u₁ u₂ v₁ v₂

variable {R : Type u₁} {T : Type u₂} [Ring R] [Ring T]
variable {M : Type v₁} {N : Type v₂}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module T N]

/-- A semilinear equivalence over a ring equivalence carries the source
socle into the target socle. -/
theorem map_moduleSocle_le_of_semilinearEquiv
    (σ : R ≃+* T)
    [RingHomInvPair σ.toRingHom σ.symm.toRingHom]
    [RingHomInvPair σ.symm.toRingHom σ.toRingHom]
    (e : M ≃ₛₗ[σ.toRingHom] N) :
    (moduleSocle R M).map e.toLinearMap ≤ moduleSocle T N := by
  rw [Submodule.map_le_iff_le_comap]
  unfold moduleSocle
  apply sSup_le
  intro U hU
  rw [← Submodule.map_le_iff_le_comap]
  exact le_moduleSocle_of_simple (U.map e.toLinearMap)
    (((e.submoduleMap U).toLinearMap.isSimpleModule_iff_of_bijective
      (e.submoduleMap U).bijective).1 hU)

/-- A semilinear equivalence over a ring equivalence carries the source
socle exactly onto the target socle. -/
theorem map_moduleSocle_eq_of_semilinearEquiv
    (σ : R ≃+* T)
    [RingHomInvPair σ.toRingHom σ.symm.toRingHom]
    [RingHomInvPair σ.symm.toRingHom σ.toRingHom]
    (e : M ≃ₛₗ[σ.toRingHom] N) :
    (moduleSocle R M).map e.toLinearMap = moduleSocle T N := by
  apply le_antisymm
  · exact map_moduleSocle_le_of_semilinearEquiv σ e
  · intro y hy
    letI : RingHomInvPair σ.symm.toRingHom σ.symm.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv σ.symm
    letI : RingHomInvPair σ.symm.symm.toRingHom σ.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm σ.symm
    have hback :
        (moduleSocle T N).map
            e.symm.toLinearMap ≤
          moduleSocle R M :=
      map_moduleSocle_le_of_semilinearEquiv σ.symm e.symm
    have hpre : e.symm y ∈ moduleSocle R M :=
      hback ⟨y, hy, rfl⟩
    exact ⟨e.symm y, hpre, e.apply_symm_apply y⟩

/-- Uniseriality is invariant under a semilinear equivalence whose scalar
map is a ring equivalence. -/
theorem isUniserialModule_iff_of_semilinearEquiv
    (σ : R ≃+* T)
    [RingHomInvPair σ.toRingHom σ.symm.toRingHom]
    [RingHomInvPair σ.symm.toRingHom σ.toRingHom]
    (e : M ≃ₛₗ[σ.toRingHom] N) :
    IsUniserialModule R M ↔ IsUniserialModule T N := by
  unfold IsUniserialModule
  let E := Submodule.orderIsoMapComap e
  constructor
  · intro h
    constructor
    intro P Q
    rcases h.total (E.symm P) (E.symm Q) with hPQ | hQP
    · exact Or.inl ((E.symm.le_iff_le).mp hPQ)
    · exact Or.inr ((E.symm.le_iff_le).mp hQP)
  · intro h
    constructor
    intro P Q
    rcases h.total (E P) (E Q) with hPQ | hQP
    · exact Or.inl ((E.le_iff_le).mp hPQ)
    · exact Or.inr ((E.le_iff_le).mp hQP)

end MagnitudeConjecture

namespace MagnitudeConjecture.RightModule

universe u

variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

/-- Applying an algebra equivalence to the elements of the right regular
module is semilinear over the induced equivalence of opposite rings. -/
def rightRegularMapAlgEquivSemilinearEquiv (f : A ≃ₐ[k] B) :
    let σ := (AlgEquiv.op f).toRingEquiv
    @LinearEquiv Aᵐᵒᵖ Bᵐᵒᵖ _ _ σ.toRingHom σ.symm.toRingHom
      (RingHomInvPair.of_ringEquiv σ)
      (RingHomInvPair.of_ringEquiv_symm σ) A B _ _ _ _ := by
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  exact
    { toFun := f
      invFun := f.symm
      left_inv := f.symm_apply_apply
      right_inv := f.apply_symm_apply
      map_add' := f.map_add
      map_smul' := by
        intro a x
        change f (x * a.unop) = f x * f a.unop
        exact f.map_mul x a.unop }

@[simp]
theorem rightRegularMapAlgEquivSemilinearEquiv_apply
    (f : A ≃ₐ[k] B) (x : A) :
    rightRegularMapAlgEquivSemilinearEquiv f x = f x :=
  by
    change f x = f x
    rfl

/-- Applying an algebra equivalence coefficientwise identifies the literal
principal right ideals semilinearly over the opposite-ring equivalence. -/
def rightIdealMapAlgEquivSemilinearEquiv (f : A ≃ₐ[k] B) (e : A) :
    let σ := (AlgEquiv.op f).toRingEquiv
    @LinearEquiv Aᵐᵒᵖ Bᵐᵒᵖ _ _ σ.toRingHom σ.symm.toRingHom
      (RingHomInvPair.of_ringEquiv σ)
      (RingHomInvPair.of_ringEquiv_symm σ)
      (rightIdeal e) (rightIdeal (f e)) _ _ _ _ := by
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  exact
    { toFun := fun x ↦ ⟨f x.1, by
          obtain ⟨a, ha⟩ := x.2
          refine ⟨f a, ?_⟩
          change f e * f a = f x.1
          change e * a = x.1 at ha
          exact (f.map_mul e a).symm.trans (congrArg f ha)⟩
      invFun := fun y ↦ ⟨f.symm y.1, by
          obtain ⟨b, hb⟩ := y.2
          refine ⟨f.symm b, ?_⟩
          change e * f.symm b = f.symm y.1
          calc
            e * f.symm b = f.symm (f e) * f.symm b := by
              rw [f.symm_apply_apply]
            _ = f.symm (f e * b) := (f.symm.map_mul (f e) b).symm
            _ = f.symm y.1 := congrArg f.symm hb⟩
      left_inv := fun x ↦ Subtype.ext (f.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (f.apply_symm_apply y.1)
      map_add' := fun x y ↦ Subtype.ext (f.map_add x.1 y.1)
      map_smul' := by
        intro a x
        apply Subtype.ext
        change f (x.1 * a.unop) = f x.1 * f a.unop
        exact f.map_mul x.1 a.unop }

@[simp]
theorem rightIdealMapAlgEquivSemilinearEquiv_apply_val
    (f : A ≃ₐ[k] B) (e : A) (x : rightIdeal e) :
    (rightIdealMapAlgEquivSemilinearEquiv f e x).1 = f x.1 :=
  by
    change f x.1 = f x.1
    rfl

/-- The restriction-of-scalars image of a finitely generated right module
has the same carrier, semilinearly identified over the opposite-ring
equivalence. -/
def fgModuleMapAlgEquivSemilinearEquiv
    (f : A ≃ₐ[k] B) (M : FinitelyGeneratedCategory A) :
    let σ := (AlgEquiv.op f).toRingEquiv
    @LinearEquiv Aᵐᵒᵖ Bᵐᵒᵖ _ _ σ.toRingHom σ.symm.toRingHom
      (RingHomInvPair.of_ringEquiv σ)
      (RingHomInvPair.of_ringEquiv_symm σ)
      M ((fgModuleEquivalenceOfAlgEquiv f).functor.obj M) _ _ _ _ := by
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  exact
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro a x
        change a • x = (AlgEquiv.op f).symm ((AlgEquiv.op f) a) • x
        rw [(AlgEquiv.op f).symm_apply_apply] }

namespace FiniteIndecomposableSkeleton

/-- Projective labels of a transported skeleton correspond without changing
their underlying finite label. -/
def mapAlgEquivProjectiveLabelEquiv
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B) :
    S.ProjectiveLabel ≃ (S.mapAlgEquiv f).ProjectiveLabel where
  toFun p := ⟨p.label, Projective.of_iso
    (S.mapAlgEquivObjIso f p.label)
      (((fgModuleEquivalenceOfAlgEquiv f).map_projective_iff
        (S.fgObj p.label)).2 p.projective)⟩
  invFun q := ⟨q.label,
    ((fgModuleEquivalenceOfAlgEquiv f).map_projective_iff
      (S.fgObj q.label)).1
        (Projective.of_iso (S.mapAlgEquivObjIso f q.label).symm
          q.projective)⟩
  left_inv p := S.projectiveLabel_eq_of_label_eq rfl
  right_inv q := (S.mapAlgEquiv f).projectiveLabel_eq_of_label_eq rfl

@[simp]
theorem mapAlgEquivProjectiveLabelEquiv_label
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel) :
    (S.mapAlgEquivProjectiveLabelEquiv f p).label = p.label :=
  rfl

/-- Injectivity of a skeletal module is unchanged by transport through an
algebra equivalence. -/
theorem fgObj_mapAlgEquiv_injective_iff
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (i : Fin S.n) :
    Injective ((S.mapAlgEquiv f).fgObj i) ↔
      Injective (S.fgObj i) := by
  let E := fgModuleEquivalenceOfAlgEquiv f
  constructor
  · intro h
    have hE : Injective (E.functor.obj (S.fgObj i)) :=
      Injective.of_iso (S.mapAlgEquivObjIso f i).symm h
    exact (E.map_injective_iff (S.fgObj i)).1 hE
  · intro h
    have hE : Injective (E.functor.obj (S.fgObj i)) :=
      (E.map_injective_iff (S.fgObj i)).2 h
    exact Injective.of_iso (S.mapAlgEquivObjIso f i) hE

/-- Uniseriality of a skeletal module is unchanged by transport through an
algebra equivalence. -/
theorem fgObj_mapAlgEquiv_isUniserial_iff
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (i : Fin S.n) :
    IsUniserialModule Bᵐᵒᵖ ((S.mapAlgEquiv f).fgObj i) ↔
      IsUniserialModule Aᵐᵒᵖ (S.fgObj i) := by
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  let e := fgModuleMapAlgEquivSemilinearEquiv f (S.fgObj i)
  constructor
  · intro h
    have hE : IsUniserialModule Bᵐᵒᵖ
        ((fgModuleEquivalenceOfAlgEquiv f).functor.obj (S.fgObj i)) :=
      IsUniserialModule.congr
        (FGModuleCat.isoToLinearEquiv
          (S.mapAlgEquivObjIso f i).symm) h
    exact (isUniserialModule_iff_of_semilinearEquiv σ e).2 hE
  · intro h
    have hE : IsUniserialModule Bᵐᵒᵖ
        ((fgModuleEquivalenceOfAlgEquiv f).functor.obj (S.fgObj i)) :=
      (isUniserialModule_iff_of_semilinearEquiv σ e).1 h
    exact IsUniserialModule.congr
      (FGModuleCat.isoToLinearEquiv
        (S.mapAlgEquivObjIso f i)) hE

namespace PrimitiveProjectivePresentation

variable {S : FiniteIndecomposableSkeleton k A}

/-- Transport a complete primitive-projective presentation through an
algebra equivalence. -/
def mapAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B) :
    (S.mapAlgEquiv f).PrimitiveProjectivePresentation where
  idempotent q :=
    f (P.idempotent ((S.mapAlgEquivProjectiveLabelEquiv f).symm q))
  complete :=
    (CompleteOrthogonalIdempotents.equiv
      (e := fun p ↦ f (P.idempotent p))
      (S.mapAlgEquivProjectiveLabelEquiv f).symm).2
        (P.complete.map f.toRingHom)
  primitive q :=
    (P.primitive ((S.mapAlgEquivProjectiveLabelEquiv f).symm q)).mapAlgEquiv f
  sourceLabel q := by
    let T := S.mapAlgEquiv f
    let e := S.mapAlgEquivProjectiveLabelEquiv f
    let p := e.symm q
    let D := (P.primitive p).mapAlgEquiv f
    apply T.projectiveLabel_eq_of_label_eq
    apply T.fgObj_skeletal
    exact ⟨
      (T.primitiveSourceIso D).symm ≪≫
        (rightIdealFGObjMapAlgEquivIso f (P.idempotent p)).symm ≪≫
        (fgModuleEquivalenceOfAlgEquiv f).functor.mapIso
          (P.primitiveProjectiveIso p) ≪≫
        S.mapAlgEquivObjIso f p.label ≪≫
        eqToIso (congrArg
          (fun r : T.ProjectiveLabel ↦ T.fgObj r.label)
          (e.apply_symm_apply q))⟩

@[simp]
theorem mapAlgEquiv_idempotent
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel) :
    (P.mapAlgEquiv f).idempotent
        (S.mapAlgEquivProjectiveLabelEquiv f p) =
      f (P.idempotent p) := by
  simp [mapAlgEquiv]

/-- The transported projective label is injective exactly when the original
label is injective. -/
theorem mapAlgEquivProjectiveLabel_injective_iff
    (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel) :
    Injective ((S.mapAlgEquiv f).fgObj
      (S.mapAlgEquivProjectiveLabelEquiv f p).label) ↔
      Injective (S.fgObj p.label) := by
  simpa using S.fgObj_mapAlgEquiv_injective_iff f p.label

/-- The transported projective label is uniserial exactly when the original
label is uniserial. -/
theorem mapAlgEquivProjectiveLabel_isUniserial_iff
    (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel) :
    IsUniserialModule Bᵐᵒᵖ ((S.mapAlgEquiv f).fgObj
      (S.mapAlgEquivProjectiveLabelEquiv f p).label) ↔
      IsUniserialModule Aᵐᵒᵖ (S.fgObj p.label) := by
  change IsUniserialModule Bᵐᵒᵖ ((S.mapAlgEquiv f).fgObj p.label) ↔
    IsUniserialModule Aᵐᵒᵖ (S.fgObj p.label)
  exact S.fgObj_mapAlgEquiv_isUniserial_iff f p.label

/-- Coefficientwise transport identifies the embedded socle of each
primitive projective right ideal. -/
theorem mem_primitiveProjectiveSocleSubmodule_mapAlgEquiv_iff
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel) (x : A) :
    f x ∈ (P.mapAlgEquiv f).primitiveProjectiveSocleSubmodule
        (S.mapAlgEquivProjectiveLabelEquiv f p) ↔
      x ∈ P.primitiveProjectiveSocleSubmodule p := by
  let σ := (AlgEquiv.op f).toRingEquiv
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm σ
  let e := rightIdealMapAlgEquivSemilinearEquiv f (P.idempotent p)
  have hsocle :
      (moduleSocle Aᵐᵒᵖ (rightIdeal (P.idempotent p))).map
          e.toLinearMap =
        moduleSocle Bᵐᵒᵖ (rightIdeal (f (P.idempotent p))) :=
    map_moduleSocle_eq_of_semilinearEquiv σ e
  constructor
  · intro hx
    change f x ∈
      (moduleSocle Bᵐᵒᵖ
        (rightIdeal ((P.mapAlgEquiv f).idempotent
          (S.mapAlgEquivProjectiveLabelEquiv f p)))).map
        (rightIdeal ((P.mapAlgEquiv f).idempotent
          (S.mapAlgEquivProjectiveLabelEquiv f p))).subtype at hx
    rw [P.mapAlgEquiv_idempotent f p] at hx
    obtain ⟨y, hySocle, hyx⟩ := (Submodule.mem_map).1 hx
    rw [← hsocle] at hySocle
    obtain ⟨z, hzSocle, hzy⟩ := (Submodule.mem_map).1 hySocle
    change x ∈
      (moduleSocle Aᵐᵒᵖ (rightIdeal (P.idempotent p))).map
        (rightIdeal (P.idempotent p)).subtype
    rw [Submodule.mem_map]
    refine ⟨z, hzSocle, f.injective ?_⟩
    calc
      f z.1 = (e z).1 := by
        rw [rightIdealMapAlgEquivSemilinearEquiv_apply_val]
      _ = y.1 := congrArg Subtype.val hzy
      _ = f x := hyx
  · intro hx
    change x ∈
      (moduleSocle Aᵐᵒᵖ (rightIdeal (P.idempotent p))).map
        (rightIdeal (P.idempotent p)).subtype at hx
    obtain ⟨z, hzSocle, hzx⟩ := (Submodule.mem_map).1 hx
    change f x ∈
      (moduleSocle Bᵐᵒᵖ
        (rightIdeal ((P.mapAlgEquiv f).idempotent
          (S.mapAlgEquivProjectiveLabelEquiv f p)))).map
        (rightIdeal ((P.mapAlgEquiv f).idempotent
          (S.mapAlgEquivProjectiveLabelEquiv f p))).subtype
    rw [P.mapAlgEquiv_idempotent f p, Submodule.mem_map]
    refine ⟨e z, ?_, ?_⟩
    · rw [← hsocle]
      exact ⟨z, hzSocle, rfl⟩
    · change (e z).1 = f x
      rw [rightIdealMapAlgEquivSemilinearEquiv_apply_val]
      exact congrArg f hzx

/-- Algebra equivalence carries each embedded primitive-projective socle
ideal to the corresponding transported ideal. -/
theorem primitiveProjectiveSocleIdeal_eq_comap_mapAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (p : S.ProjectiveLabel)
    (hp : Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleIdeal p hp =
      ((P.mapAlgEquiv f).primitiveProjectiveSocleIdeal
        (S.mapAlgEquivProjectiveLabelEquiv f p)
        ((mapAlgEquivProjectiveLabel_injective_iff f p).2 hp)).comap f := by
  apply TwoSidedIdeal.ext
  intro x
  rw [P.mem_primitiveProjectiveSocleIdeal,
    TwoSidedIdeal.mem_comap,
    (P.mapAlgEquiv f).mem_primitiveProjectiveSocleIdeal]
  exact (P.mem_primitiveProjectiveSocleSubmodule_mapAlgEquiv_iff f p x).symm

/-- Transport a finite family of projective labels through an algebra
equivalence. -/
def mapAlgEquivProjectiveLabels
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel) :
    Finset (S.mapAlgEquiv f).ProjectiveLabel :=
  T.map (S.mapAlgEquivProjectiveLabelEquiv f).toEmbedding

@[simp]
theorem mem_mapAlgEquivProjectiveLabels
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel) (p : S.ProjectiveLabel) :
    S.mapAlgEquivProjectiveLabelEquiv f p ∈
        mapAlgEquivProjectiveLabels S f T ↔
      p ∈ T := by
  simp [mapAlgEquivProjectiveLabels]

/-- Injectivity data for a selected projective family transports label by
label. -/
def mapAlgEquivProjectiveLabels_injective
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    ∀ q, q ∈ mapAlgEquivProjectiveLabels S f T →
      Injective ((S.mapAlgEquiv f).fgObj q.label) := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_map.1 hq
  subst q
  exact (mapAlgEquivProjectiveLabel_injective_iff f p).2
    (hInjective p hp)

/-- The simultaneous socle-family ideal depends on the selected finset, not
on the proof term certifying injectivity of its members. -/
theorem primitiveProjectiveSocleFamilyIdeal_congr
    (P : S.PrimitiveProjectivePresentation)
    {T U : Finset S.ProjectiveLabel} (hTU : T = U)
    (hT : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hU : ∀ p, p ∈ U → Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleFamilyIdeal T hT =
      P.primitiveProjectiveSocleFamilyIdeal U hU := by
  subst U
  rfl

/-- Algebra equivalence transports the simultaneous socle-family ideal. -/
theorem primitiveProjectiveSocleFamilyIdeal_eq_comap_mapAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    P.primitiveProjectiveSocleFamilyIdeal T hInjective =
      ((P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
        (mapAlgEquivProjectiveLabels S f T)
        (mapAlgEquivProjectiveLabels_injective S f T hInjective)).comap f := by
  let T' := mapAlgEquivProjectiveLabels S f T
  let hInjective' := mapAlgEquivProjectiveLabels_injective S f T hInjective
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let J' := (P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal T' hInjective'
  change J = J'.comap f
  apply le_antisymm
  · change (⨆ p : {p // p ∈ T},
        P.primitiveProjectiveSocleIdeal p.1
          (hInjective p.1 p.2)) ≤ J'.comap f
    apply iSup_le
    rintro ⟨p, hp⟩
    rw [P.primitiveProjectiveSocleIdeal_eq_comap_mapAlgEquiv f p
      (hInjective p hp)]
    intro x hx
    rw [TwoSidedIdeal.mem_comap] at hx ⊢
    exact (le_iSup
        (fun q : {q // q ∈ T'} ↦
          (P.mapAlgEquiv f).primitiveProjectiveSocleIdeal q.1
            (hInjective' q.1 q.2))
        ⟨S.mapAlgEquivProjectiveLabelEquiv f p, by
          exact (mem_mapAlgEquivProjectiveLabels S f T p).2 hp⟩) hx
  · intro x hx
    have hJ' : J' ≤ J.comap f.symm := by
      change (⨆ q : {q // q ∈ T'},
          (P.mapAlgEquiv f).primitiveProjectiveSocleIdeal q.1
            (hInjective' q.1 q.2)) ≤ J.comap f.symm
      apply iSup_le
      rintro ⟨q, hq⟩
      obtain ⟨p, hp, hpq⟩ := Finset.mem_map.1 hq
      subst q
      intro y hy
      rw [TwoSidedIdeal.mem_comap]
      change f.symm y ∈ J
      apply P.primitiveProjectiveSocleIdeal_le_familyIdeal
        T hInjective p hp
      rw [P.primitiveProjectiveSocleIdeal_eq_comap_mapAlgEquiv f p
        (hInjective p hp), TwoSidedIdeal.mem_comap]
      simpa using hy
    rw [TwoSidedIdeal.mem_comap] at hx
    have hx' := hJ' hx
    rw [TwoSidedIdeal.mem_comap] at hx'
    simpa using hx'

/-- Ring congruences of the simultaneous socle-family quotients are
transported by the ambient algebra equivalence. -/
theorem primitiveProjectiveSocleFamilyIdeal_ringCon_eq_comap_mapAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    (P.primitiveProjectiveSocleFamilyIdeal T hInjective).ringCon =
      ((P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
        (mapAlgEquivProjectiveLabels S f T)
        (mapAlgEquivProjectiveLabels_injective S f T hInjective)).ringCon.comap f := by
  change (P.primitiveProjectiveSocleFamilyIdeal T hInjective).ringCon =
    (((P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
      (mapAlgEquivProjectiveLabels S f T)
      (mapAlgEquivProjectiveLabels_injective S f T hInjective)).comap f).ringCon
  rw [P.primitiveProjectiveSocleFamilyIdeal_eq_comap_mapAlgEquiv
    f T hInjective]

/-- Algebra equivalence transports the literal quotient by a simultaneous
primitive-projective socle family. -/
def primitiveProjectiveSocleFamilyQuotientAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B)
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective) ≃ₐ[k]
      idealQuotientAlgebra
        ((P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
          (mapAlgEquivProjectiveLabels S f T)
          (mapAlgEquivProjectiveLabels_injective S f T hInjective)) :=
  RingCon.congrₐ k f
    (P.primitiveProjectiveSocleFamilyIdeal_ringCon_eq_comap_mapAlgEquiv
      f T hInjective)

end PrimitiveProjectivePresentation

end FiniteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
