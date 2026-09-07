import MagnitudeConjecture.CategoryTheory.MeshCoveringHom

/-!
# Lifting mesh ideals along polarized quiver coverings

This file proves the relation-lifting statement left open by the quotient
squares for mesh coverings.  The first half treats the fixed-target Hom map:
a path-basis composite through a target mesh lifts to one source mesh
composite in a uniquely determined fibre component.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u v₁ v₂ w₁ w₂

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]

namespace RightMeshData.Cover

variable {T₁ : RightMeshData Q₁} {T₂ : RightMeshData Q₂}
variable {k : Type u} [Field k]

/-- A vertex over the translated end of a nonempty target mesh is itself the
translate of a uniquely determined lift of the mesh vertex. -/
theorem exists_lifted_nonprojective_of_tau_fiber
    (C : RightMeshData.Cover T₁ T₂)
    (s : {z : Q₂ // z ∉ T₂.projective}) (t : Q₁)
    (ht : C.toPrefunctor.obj t = T₂.tau s)
    (a : T₂.MeshArrow s) :
    ∃ s₁ : {z : Q₁ // z ∉ T₁.projective},
      C.mapNonprojective s₁ = s ∧ T₁.tau s₁ = t := by
  classical
  let rLift :=
    (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
      C.toPrefunctor C.isCovering t s.1).symm
        ((T₂.meshPath s a).cast rfl ht.symm)
  have hr :
      (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
        C.toPrefunctor C.isCovering t s.1) rLift =
          (T₂.meshPath s a).cast rfl ht.symm := by
    dsimp only [rLift]
    exact Equiv.apply_symm_apply
      (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
        C.toPrefunctor C.isCovering t s.1)
      ((T₂.meshPath s a).cast rfl ht.symm)
  obtain ⟨⟨s₁, hs₁⟩, r₁⟩ := rLift
  have hs₁_nonprojective : s₁ ∉ T₁.projective := by
    intro hs₁_projective
    apply s.2
    rw [← hs₁]
    exact (C.map_projective_iff s₁).1 hs₁_projective
  let s₁' : {z : Q₁ // z ∉ T₁.projective} :=
    ⟨s₁, hs₁_nonprojective⟩
  have hs : C.mapNonprojective s₁' = s := Subtype.ext hs₁
  subst s
  let a₁ : T₁.MeshArrow s₁' := (C.meshArrowEquiv s₁').symm a
  let U : Σ Z : {z : Q₁ // C.toPrefunctor.obj z =
      T₂.tau (C.mapNonprojective s₁')}, Quiver.Path s₁ Z.1 :=
    ⟨⟨t, ht⟩, r₁⟩
  let V : Σ Z : {z : Q₁ // C.toPrefunctor.obj z =
      T₂.tau (C.mapNonprojective s₁')}, Quiver.Path s₁ Z.1 :=
    ⟨⟨T₁.tau s₁', C.map_tau s₁'⟩, T₁.meshPath s₁' a₁⟩
  have hUV : U = V := by
    apply (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
      C.toPrefunctor C.isCovering
        (T₂.tau (C.mapNonprojective s₁')) s₁).injective
    simp only [MagnitudeConjecture.LinearPathCategory.sourcePathEquiv_apply,
      MagnitudeConjecture.LinearPathCategory.sourcePathMap]
    dsimp only [U, V]
    simp only [MagnitudeConjecture.LinearPathCategory.targetPathEquiv_apply,
      MagnitudeConjecture.LinearPathCategory.targetPathMap] at hr
    have hr' : (C.toPrefunctor.mapPath r₁).cast rfl ht =
        T₂.meshPath (C.mapNonprojective s₁') a := by
      apply (Quiver.Path.cast_eq_iff_heq rfl ht _ _).2
      exact (Quiver.Path.cast_heq hs₁ rfl
        (C.toPrefunctor.mapPath r₁)).symm.trans
          ((heq_of_eq hr).trans
            (Quiver.Path.cast_heq rfl ht.symm
              (T₂.meshPath (C.mapNonprojective s₁') a)))
    rw [hr', C.mapPath_meshPath]
    have ha₁ : C.meshArrowMap s₁' a₁ = a := by
      exact (C.meshArrowEquiv s₁').apply_symm_apply a
    rw [ha₁]
  have htau : t = T₁.tau s₁' :=
    congrArg (fun W ↦ W.1.1) hUV
  exact ⟨s₁', rfl, htau.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- A path-basis composite through one target mesh has a free fixed-target
preimage supported in one fibre component, and that preimage belongs to the
source mesh ideal. -/
theorem source_basisComposite_has_ideal_preimage
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₂) (y : Q₁)
    {f : MagnitudeConjecture.LinearPathCategory.obj k Q₂ x ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj y)}
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T₂.meshGeneratorSet (k := k))
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x)
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj y))) :
    letI := C.sourceStarFintype
    ∃ a : DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y),
      C.sourceFreeFiberHomMap (k := k) x y a = f ∧
        C.sourceFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  classical
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  rcases hr with ⟨s, hA, hB, hr⟩
  subst A
  subst B
  subst r
  let qLift :=
    (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
      C.toPrefunctor C.isCovering s.1 y).symm q
  have hq :
      (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
        C.toPrefunctor C.isCovering s.1 y) qLift = q := by
    dsimp only [qLift]
    exact Equiv.apply_symm_apply
      (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
        C.toPrefunctor C.isCovering s.1 y) q
  obtain ⟨⟨s₁, hs₁⟩, q₁⟩ := qLift
  have hs₁_nonprojective : s₁ ∉ T₁.projective := by
    intro hs₁_projective
    apply s.2
    rw [← hs₁]
    exact (C.map_projective_iff s₁).1 hs₁_projective
  let s₁' : {z : Q₁ // z ∉ T₁.projective} :=
    ⟨s₁, hs₁_nonprojective⟩
  have hs : C.mapNonprojective s₁' = s := Subtype.ext hs₁
  subst s
  let pLift :=
    (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
      C.toPrefunctor C.isCovering x (T₁.tau s₁')).symm
        (p.cast (C.map_tau s₁').symm rfl)
  have hp :
      (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
        C.toPrefunctor C.isCovering x (T₁.tau s₁')) pLift =
          p.cast (C.map_tau s₁').symm rfl := by
    dsimp only [pLift]
    exact Equiv.apply_symm_apply
      (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
        C.toPrefunctor C.isCovering x (T₁.tau s₁'))
          (p.cast (C.map_tau s₁').symm rfl)
  obtain ⟨⟨z, hz⟩, p₁⟩ := pLift
  let Z : MagnitudeConjecture.LinearCovering.Fiber
      (C.functor (k := k)) (obj (k := k) T₂ x) :=
    ⟨obj (k := k) T₁ z, congrArg (obj (k := k) T₂) hz⟩
  let g : Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y :=
    MagnitudeConjecture.LinearPathCategory.pathHom p₁ ≫
      T₁.meshRelation (k := k) s₁' ≫
        MagnitudeConjecture.LinearPathCategory.pathHom q₁
  let a := C.sourceFreeFiberLof (k := k) x y Z g
  refine ⟨a, ?_, ?_⟩
  · dsimp only [a]
    rw [C.sourceFreeFiberHomMap_lof (k := k)]
    change eqToHom (congrArg
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂) hz).symm ≫
        (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) C.toPrefunctor).map g = _
    dsimp only [g]
    rw [Functor.map_comp, Functor.map_comp,
      MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom,
      C.prefunctorFunctor_map_meshRelation (k := k),
      MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    simp only [Category.assoc]
    simp only [MagnitudeConjecture.LinearPathCategory.sourcePathEquiv_apply,
      MagnitudeConjecture.LinearPathCategory.sourcePathMap] at hq hp
    rw [← Category.assoc]
    rw [MagnitudeConjecture.LinearPathCategory.eqToHom_comp_pathHom_eq_cast_end
      (k := k) (Q₂ := Q₂) (C.toPrefunctor.mapPath p₁) hz]
    rw [hp]
    rw [← Category.assoc]
    rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
      (k := k) (Q₂ := Q₂)
      (p.cast (C.map_tau s₁').symm rfl) (C.map_tau s₁')]
    have hq' : C.toPrefunctor.mapPath q₁ = q := by
      simpa using hq
    rw [hq']
    simp
  · dsimp only [a]
    rw [C.sourceFiberQuotientMap_lof (k := k)]
    have hg : g ∈ T₁.meshIdealHom (k := k) z y := by
      exact HomIdeal.composite_mem_linearSpan
        (T₁.meshGeneratorSet (k := k))
        (MagnitudeConjecture.LinearPathCategory.pathHom p₁)
        (T₁.meshRelation_mem_meshGeneratorSet (k := k) s₁')
        (MagnitudeConjecture.LinearPathCategory.pathHom q₁)
    rw [C.sourceComponentQuotientMap_eq_zero_of_mem_meshIdealHom
      (k := k) x y Z g hg]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- A path-basis composite through one target mesh has a free fixed-source
preimage supported in one fibre component, and that preimage belongs to the
source mesh ideal. -/
theorem target_basisComposite_has_ideal_preimage
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₁) (y : Q₂)
    {f : MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj x) ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₂ y}
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T₂.meshGeneratorSet (k := k))
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj x))
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ y)) :
    letI := C.sourceStarFintype
    ∃ a : DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as),
      C.targetFreeFiberHomMap (k := k) x y a = f ∧
        C.targetFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  classical
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  rcases hr with ⟨s, hA, hB, hr⟩
  subst A
  subst B
  subst r
  cases isEmpty_or_nonempty (T₂.MeshArrow s) with
  | inl hempty =>
      letI := hempty
      refine ⟨0, ?_, by simp⟩
      simp [RightMeshData.meshRelation]
  | inr hnonempty =>
      let a₂ : T₂.MeshArrow s := Classical.choice hnonempty
      let pLift :=
        (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
          C.toPrefunctor C.isCovering x (T₂.tau s)).symm p
      have hp :
          (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
            C.toPrefunctor C.isCovering x (T₂.tau s)) pLift = p := by
        dsimp only [pLift]
        exact Equiv.apply_symm_apply
          (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
            C.toPrefunctor C.isCovering x (T₂.tau s)) p
      obtain ⟨⟨t, ht⟩, p₁⟩ := pLift
      obtain ⟨s₁, hs, htau⟩ :=
        C.exists_lifted_nonprojective_of_tau_fiber s t ht a₂
      subst t
      subst s
      let qLift :=
        (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
          C.toPrefunctor C.isCovering s₁.1 y).symm q
      have hq :
          (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
            C.toPrefunctor C.isCovering s₁.1 y) qLift = q := by
        dsimp only [qLift]
        exact Equiv.apply_symm_apply
          (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
            C.toPrefunctor C.isCovering s₁.1 y) q
      obtain ⟨⟨z, hz⟩, q₁⟩ := qLift
      let Z : MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y) :=
        ⟨obj (k := k) T₁ z, congrArg (obj (k := k) T₂) hz⟩
      let g : MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as :=
        MagnitudeConjecture.LinearPathCategory.pathHom p₁ ≫
          T₁.meshRelation (k := k) s₁ ≫
            MagnitudeConjecture.LinearPathCategory.pathHom q₁
      let b := C.targetFreeFiberLof (k := k) x y Z g
      refine ⟨b, ?_, ?_⟩
      · dsimp only [b]
        rw [C.targetFreeFiberHomMap_lof (k := k)]
        change (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
            (k := k) C.toPrefunctor).map g ≫
            eqToHom (congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k Q₂) hz) = _
        dsimp only [g]
        rw [Functor.map_comp, Functor.map_comp,
          MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom,
          C.prefunctorFunctor_map_meshRelation (k := k),
          MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        simp only [Category.assoc]
        simp only [MagnitudeConjecture.LinearPathCategory.targetPathEquiv_apply,
          MagnitudeConjecture.LinearPathCategory.targetPathMap] at hp hq
        rw [← Category.assoc]
        rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
          (k := k) (Q₂ := Q₂) (C.toPrefunctor.mapPath p₁) (C.map_tau s₁)]
        rw [hp]
        rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
          (k := k) (Q₂ := Q₂) (C.toPrefunctor.mapPath q₁) hz]
        rw [hq]
      · dsimp only [b]
        rw [C.targetFiberQuotientMap_lof (k := k)]
        have hg : g ∈ T₁.meshIdealHom (k := k) x z := by
          exact HomIdeal.composite_mem_linearSpan
            (T₁.meshGeneratorSet (k := k))
            (MagnitudeConjecture.LinearPathCategory.pathHom p₁)
            (T₁.meshRelation_mem_meshGeneratorSet (k := k) s₁)
            (MagnitudeConjecture.LinearPathCategory.pathHom q₁)
        rw [C.targetComponentQuotientMap_eq_zero_of_mem_meshIdealHom
          (k := k) x y Z g hg]
        simp

/-- Every target mesh-ideal element has a free fixed-source preimage which is
already zero after componentwise quotienting by the source mesh ideal. -/
theorem target_meshIdeal_has_ideal_preimage
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₁) (y : Q₂)
    {f : MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj x) ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₂ y}
    (hf : f ∈ T₂.meshIdealHom (k := k) (C.toPrefunctor.obj x) y) :
    letI := C.sourceStarFintype
    ∃ a : DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as),
      C.targetFreeFiberHomMap (k := k) x y a = f ∧
        C.targetFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  classical
  change f ∈ HomIdeal.generatedHomSubmodule k
    (T₂.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q₂
      (C.toPrefunctor.obj x))
    (MagnitudeConjecture.LinearPathCategory.obj k Q₂ y) at hf
  rw [MagnitudeConjecture.LinearPathCategory.generatedHomSubmodule_eq_span_basisCompositeSet]
    at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      exact C.target_basisComposite_has_ideal_preimage (k := k) x y hf
  | zero =>
      exact ⟨0, by simp, by simp⟩
  | add f g _ _ hf hg =>
      rcases hf with ⟨a, ha, ha0⟩
      rcases hg with ⟨b, hb, hb0⟩
      refine ⟨a + b, ?_, ?_⟩
      · simp only [map_add, ha, hb]
      · simp only [map_add, ha0, hb0, add_zero]
  | smul r f _ hf =>
      rcases hf with ⟨a, ha, ha0⟩
      refine ⟨r • a, ?_, ?_⟩
      · simp only [map_smul, ha]
      · simp only [map_smul, ha0, smul_zero]

/-- The fixed-source half of mesh-ideal lifting holds for every polarized
quiver covering. -/
theorem target_meshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₁) (y : Q₂)
    (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as)) :
    letI := C.sourceStarFintype
    (quotientFunctor (k := k) T₂).map
        (C.targetFreeFiberHomMap (k := k) x y a) = 0 →
      C.targetFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  intro ha
  have hideal : C.targetFreeFiberHomMap (k := k) x y a ∈
      T₂.meshIdealHom (k := k) (C.toPrefunctor.obj x) y :=
    (T₂.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k)
      (C.toPrefunctor.obj x) y
      (C.targetFreeFiberHomMap (k := k) x y a)).1 ha
  obtain ⟨b, hb, hb0⟩ :=
    C.target_meshIdeal_has_ideal_preimage (k := k) x y hideal
  have hba : b = a := by
    apply (C.targetFreeFiberHomEquiv (k := k) x y).injective
    change (C.targetFreeFiberHomEquiv (k := k) x y).toLinearMap b =
      (C.targetFreeFiberHomEquiv (k := k) x y).toLinearMap a
    rw [C.targetFreeFiberHomEquiv_eq_map (k := k)]
    exact hb
  rw [← hba]
  exact hb0

/-- Every target mesh-ideal element has a free fixed-target preimage which is
already zero after componentwise quotienting by the source mesh ideal. -/
theorem source_meshIdeal_has_ideal_preimage
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₂) (y : Q₁)
    {f : MagnitudeConjecture.LinearPathCategory.obj k Q₂ x ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj y)}
    (hf : f ∈ T₂.meshIdealHom (k := k) x (C.toPrefunctor.obj y)) :
    letI := C.sourceStarFintype
    ∃ a : DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y),
      C.sourceFreeFiberHomMap (k := k) x y a = f ∧
        C.sourceFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  classical
  change f ∈ HomIdeal.generatedHomSubmodule k
    (T₂.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q₂
      (C.toPrefunctor.obj y)) at hf
  rw [MagnitudeConjecture.LinearPathCategory.generatedHomSubmodule_eq_span_basisCompositeSet]
    at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      exact C.source_basisComposite_has_ideal_preimage (k := k) x y hf
  | zero =>
      exact ⟨0, by simp, by simp⟩
  | add f g _ _ hf hg =>
      rcases hf with ⟨a, ha, ha0⟩
      rcases hg with ⟨b, hb, hb0⟩
      refine ⟨a + b, ?_, ?_⟩
      · simp only [map_add, ha, hb]
      · simp only [map_add, ha0, hb0, add_zero]
  | smul r f _ hf =>
      rcases hf with ⟨a, ha, ha0⟩
      refine ⟨r • a, ?_, ?_⟩
      · simp only [map_smul, ha]
      · simp only [map_smul, ha0, smul_zero]

/-- The fixed-target half of mesh-ideal lifting holds for every polarized
quiver covering. -/
theorem source_meshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)]
    (x : Q₂) (y : Q₁)
    (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)) :
    letI := C.sourceStarFintype
    (quotientFunctor (k := k) T₂).map
        (C.sourceFreeFiberHomMap (k := k) x y a) = 0 →
      C.sourceFiberQuotientMap (k := k) x y a = 0 := by
  letI := C.sourceStarFintype
  intro ha
  have hideal : C.sourceFreeFiberHomMap (k := k) x y a ∈
      T₂.meshIdealHom (k := k) x (C.toPrefunctor.obj y) :=
    (T₂.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k)
      x (C.toPrefunctor.obj y)
      (C.sourceFreeFiberHomMap (k := k) x y a)).1 ha
  obtain ⟨b, hb, hb0⟩ :=
    C.source_meshIdeal_has_ideal_preimage (k := k) x y hideal
  have hba : b = a := by
    apply (C.sourceFreeFiberHomEquiv (k := k) x y).injective
    change (C.sourceFreeFiberHomEquiv (k := k) x y).toLinearMap b =
      (C.sourceFreeFiberHomEquiv (k := k) x y).toLinearMap a
    rw [C.sourceFreeFiberHomEquiv_eq_map (k := k)]
    exact hb
  rw [← hba]
  exact hb0

/-- Every polarized quiver covering lifts the generated mesh ideal in both
Hom variables. -/
theorem hasMeshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)] :
    letI := C.sourceStarFintype
    C.HasMeshIdealLifting (k := k) := by
  letI := C.sourceStarFintype
  constructor
  · intro x y a
    exact C.target_meshIdealLifting (k := k) x y a
  · intro x y a
    exact C.source_meshIdealLifting (k := k) x y a

/-- A covering of polarized right translation quivers induces a Bongartz--
Gabriel covering functor between their mesh categories. -/
theorem functor_isCovering
    (C : RightMeshData.Cover T₁ T₂)
    [∀ z : Q₂, Fintype (Quiver.Star z)] :
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (C.functor (k := k)) := by
  letI := C.sourceStarFintype
  exact C.functor_isCovering_of_hasMeshIdealLifting
    (k := k) (C.hasMeshIdealLifting (k := k))

/-- The ambient-source version of the mesh functor is also a Bongartz--
Gabriel covering.  The only comparison needed is uniqueness of the
`Fintype` structure on each arrow star. -/
theorem functorUsingSourceFintype_isCovering
    (C : RightMeshData.Cover T₁ T₂)
    [sourceStarFintype : ∀ z : Q₁, Fintype (Quiver.Star z)]
    [∀ z : Q₂, Fintype (Quiver.Star z)] :
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (C.functorUsingSourceFintype (k := k)) := by
  have hsource : sourceStarFintype = C.sourceStarFintype :=
    Subsingleton.elim _ _
  subst sourceStarFintype
  exact C.functor_isCovering (k := k)

end RightMeshData.Cover

end MagnitudeConjecture.MeshCategory
