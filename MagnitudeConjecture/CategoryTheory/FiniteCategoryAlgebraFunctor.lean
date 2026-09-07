import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-!
# Finite category algebras under full linear functors

A linear functor between finite linear categories acts entrywise on the
Yoneda-coordinate matrices of their representable projective generators.
This file packages that construction as an algebra homomorphism.  Unlike the
existing category-algebra equivalence, faithfulness is not required: quotient
functors therefore give quotient maps of category algebras.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k C D : Type u} [Field k]
variable [Category.{u} C] [Preadditive C] [Linear k C]
variable [Category.{u} D] [Preadditive D] [Linear k D]
variable [Fintype C]

namespace finiteCategoryProjectiveGenerator

variable
    (hC : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hD : ∀ X : D, IsFiniteDimensionalModule (C := D) k
      (linearCoyonedaLinearModule (k := k) X))
    (F : C ⥤ D) [F.Additive] [F.Linear k]

private abbrev representable {E : Type u} [Category.{u} E]
    [Preadditive E] [Linear k E]
    (hE : ∀ X : E, IsFiniteDimensionalModule (C := E) k
      (linearCoyonedaLinearModule (k := k) X)) (X : E) :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hE).obj (Opposite.op X)

/-- A small finite index for the objects of the source category. -/
abbrev SmallIndex := Fin (Fintype.card C)

private abbrev sourceSmallGenerator :=
  ⨁ fun i : SmallIndex (C := C) ↦
    representable (E := C) hC ((Fintype.equivFin C).symm i)

/-- The sum of the target representables indexed through a small enumeration
of the source objects. -/
abbrev mappedGenerator :=
  ⨁ fun i : SmallIndex (C := C) ↦
    representable (E := D) hD (F.obj ((Fintype.equivFin C).symm i))

/-- The endomorphism algebra of the source-indexed sum of target
representables. -/
abbrev mappedAlgebra := End (mappedGenerator hD F)

/-- Apply a linear functor to the Yoneda coordinate of a morphism between
representables. -/
private def mapRepresentableHom (X Y : C)
    (f : representable (E := C) hC X ⟶ representable (E := C) hC Y) :
    representable (E := D) hD (F.obj X) ⟶
      representable (E := D) hD (F.obj Y) :=
  ObjectProperty.homMk
    (linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (F.map (f.hom.hom.app X (𝟙 X))))

private theorem mapRepresentableHom_add (X Y : C)
    (f g : representable (E := C) hC X ⟶ representable (E := C) hC Y) :
    mapRepresentableHom hC hD F X Y (f + g) =
      mapRepresentableHom hC hD F X Y f +
        mapRepresentableHom hC hD F X Y g := by
  apply ObjectProperty.hom_ext
  let a : Y ⟶ X := f.hom.hom.app X (𝟙 X)
  let b : Y ⟶ X := g.hom.hom.app X (𝟙 X)
  change linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (F.map (a + b)) =
    linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
        (F.map a) +
      linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
        (F.map b)
  rw [F.map_add]
  exact (linearCoyonedaHomEquiv
    (representable (E := D) hD (F.obj Y)).obj (F.obj X)).symm.map_add _ _

private theorem mapRepresentableHom_smul (X Y : C) (c : k)
    (f : representable (E := C) hC X ⟶ representable (E := C) hC Y) :
    mapRepresentableHom hC hD F X Y (c • f) =
      c • mapRepresentableHom hC hD F X Y f := by
  apply ObjectProperty.hom_ext
  let a : Y ⟶ X := f.hom.hom.app X (𝟙 X)
  change linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (F.map (c • a)) =
    c • linearCoyonedaHom (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (F.map a)
  rw [F.map_smul]
  exact (linearCoyonedaHomEquiv
    (representable (E := D) hD (F.obj Y)).obj (F.obj X)).symm.map_smul c _

private theorem mapRepresentableHom_zero (X Y : C) :
    mapRepresentableHom hC hD F X Y 0 = 0 := by
  simpa only [smul_zero, zero_smul] using
    mapRepresentableHom_smul hC hD F X Y (0 : k) 0

private theorem mapRepresentableHom_id (X : C) :
    mapRepresentableHom hC hD F X X (𝟙 _) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  change linearCoyonedaHom
    (representable (E := D) hD (F.obj X)).obj (F.obj X)
      (F.map (𝟙 X)) = 𝟙 _
  rw [F.map_id]
  exact linearCoyonedaHom_self
    (representable (E := D) hD (F.obj X)).obj (F.obj X) (𝟙 _)

private theorem source_coordinate_comp (X Y Z : C)
    (f : representable (E := C) hC X ⟶ representable (E := C) hC Y)
    (g : representable (E := C) hC Y ⟶ representable (E := C) hC Z) :
    (f ≫ g).hom.hom.app X (𝟙 X) =
      g.hom.hom.app Y (𝟙 Y) ≫ f.hom.hom.app X (𝟙 X) := by
  change g.hom.hom.app X (f.hom.hom.app X (𝟙 X)) = _
  let a : Y ⟶ X := f.hom.hom.app X (𝟙 X)
  have hnat := ConcreteCategory.congr_hom (g.hom.hom.naturality a) (𝟙 Y)
  change g.hom.hom.app X ((𝟙 Y) ≫ a) =
    g.hom.hom.app Y (𝟙 Y) ≫ a at hnat
  simpa only [Category.id_comp] using hnat

private theorem mapRepresentableHom_comp (X Y Z : C)
    (f : representable (E := C) hC X ⟶ representable (E := C) hC Y)
    (g : representable (E := C) hC Y ⟶ representable (E := C) hC Z) :
    mapRepresentableHom hC hD F X Z (f ≫ g) =
      mapRepresentableHom hC hD F X Y f ≫
        mapRepresentableHom hC hD F Y Z g := by
  apply ObjectProperty.hom_ext
  let a : Y ⟶ X := f.hom.hom.app X (𝟙 X)
  let b : Z ⟶ Y := g.hom.hom.app Y (𝟙 Y)
  change linearCoyonedaHom
      (representable (E := D) hD (F.obj Z)).obj (F.obj X)
      (F.map ((f ≫ g).hom.hom.app X (𝟙 X))) = _
  rw [source_coordinate_comp hC X Y Z f g]
  change linearCoyonedaHom
      (representable (E := D) hD (F.obj Z)).obj (F.obj X)
      (F.map (b ≫ a)) = _
  rw [F.map_comp]
  change linearCoyonedaHom
      (representable (E := D) hD (F.obj Z)).obj (F.obj X)
        (F.map b ≫ F.map a) =
    linearCoyonedaHom
        (representable (E := D) hD (F.obj Y)).obj (F.obj X)
          (F.map a) ≫
      linearCoyonedaHom
        (representable (E := D) hD (F.obj Z)).obj (F.obj Y)
          (F.map b)
  have h := linearCoyonedaHom_comp
    (representable (E := D) hD (F.obj Y)).obj
    (representable (E := D) hD (F.obj Z)).obj
    (F.obj X) (F.map a)
    (linearCoyonedaHom
      (representable (E := D) hD (F.obj Z)).obj (F.obj Y) (F.map b))
  have happ :
      (linearCoyonedaHom
          (representable (E := D) hD (F.obj Z)).obj (F.obj Y)
          (F.map b)).hom.app (F.obj X) (F.map a) =
        F.map b ≫ F.map a := rfl
  have hr := congrArg
    (linearCoyonedaHom (representable (E := D) hD (F.obj Z)).obj (F.obj X))
    happ
  exact (h.trans hr).symm

private def preimageRepresentableHom [F.Full] (X Y : C)
    (g : representable (E := D) hD (F.obj X) ⟶
      representable (E := D) hD (F.obj Y)) :
    representable (E := C) hC X ⟶ representable (E := C) hC Y :=
  ObjectProperty.homMk
    (linearCoyonedaHom (representable (E := C) hC Y).obj X
      (F.preimage (g.hom.hom.app (F.obj X) (𝟙 (F.obj X)))))

private theorem mapRepresentableHom_preimage [F.Full] (X Y : C)
    (g : representable (E := D) hD (F.obj X) ⟶
      representable (E := D) hD (F.obj Y)) :
    mapRepresentableHom hC hD F X Y
      (preimageRepresentableHom hC hD F X Y g) = g := by
  apply ObjectProperty.hom_ext
  let a : F.obj Y ⟶ F.obj X :=
    g.hom.hom.app (F.obj X) (𝟙 (F.obj X))
  let b : Y ⟶ X := F.preimage a
  change linearCoyonedaHom
      (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (F.map ((linearCoyonedaHom
        (representable (E := C) hC Y).obj X
        b).hom.app X
          (𝟙 X))) = g.hom
  have hb :
      (linearCoyonedaHom (representable (E := C) hC Y).obj X b).hom.app X
          (𝟙 X) = b :=
    linearCoyonedaHom_app_id
      (representable (E := C) hC Y).obj X b
  rw [hb]
  have hFb : F.map b = a := F.map_preimage a
  rw [hFb]
  change linearCoyonedaHom
      (representable (E := D) hD (F.obj Y)).obj (F.obj X)
      (g.hom.hom.app (F.obj X) (𝟙 (F.obj X))) = g.hom
  exact linearCoyonedaHom_self
    (representable (E := D) hD (F.obj Y)).obj (F.obj X) g.hom

/-- Reindex the possibly large finite object type by the small type
`Fin (card C)`. -/
def generatorSmallIso :
    finiteCategoryProjectiveGenerator hC ≅ sourceSmallGenerator hC := by
  let e := Fintype.equivFin C
  let Q := fun X : C ↦ representable (E := C) hC X
  let Qs := fun i : SmallIndex (C := C) ↦ Q (e.symm i)
  refine {
    hom := biproduct.desc fun X ↦
      eqToHom (by
        change representable (E := C) hC X =
          representable (E := C) hC (e.symm (e X))
        rw [e.symm_apply_apply]) ≫
        biproduct.ι
          (fun i : SmallIndex (C := C) ↦
            representable (E := C) hC ((Fintype.equivFin C).symm i)) (e X)
    inv := biproduct.desc fun i ↦ biproduct.ι Q (e.symm i)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply biproduct.hom_ext'
    intro X
    apply biproduct.hom_ext
    intro Y
    by_cases hXY : X = Y
    · subst Y
      simp only [biproduct.ι_desc_assoc, Category.assoc]
      rw [← Category.assoc]
      rw [biproduct.eqToHom_comp_ι Q (e.symm_apply_apply X).symm]
      simpa only [Q, Category.comp_id, Category.id_comp] using
        biproduct.ι_π_self Q X
    · simp [Q, Qs, e, hXY]
  · apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    by_cases hij : i = j
    · subst j
      simp only [biproduct.ι_desc_assoc, Category.assoc]
      rw [← Category.assoc]
      rw [biproduct.eqToHom_comp_ι Qs (e.apply_symm_apply i).symm]
      simpa only [Qs, Q, e, Category.comp_id, Category.id_comp] using
        biproduct.ι_π_self Qs i
    · simp [Q, Qs, e, hij]

/-- The projector onto one representable summand, indexed by the small
enumeration `Fin (card C)` of the possibly large finite object type. -/
def smallCanonicalProjector (i : SmallIndex (C := C)) : algebra hC :=
  let X := (Fintype.equivFin C).symm i
  biproduct.π (fun Y : C ↦ representable (E := C) hC Y) X ≫
    biproduct.ι (fun Y : C ↦ representable (E := C) hC Y) X

theorem generatorSmallIso_hom_comp_π
    (i : SmallIndex (C := C)) :
    (generatorSmallIso hC).hom ≫
        biproduct.π
          (fun j : SmallIndex (C := C) ↦
            representable (E := C) hC ((Fintype.equivFin C).symm j)) i =
      biproduct.π (fun Y : C ↦ representable (E := C) hC Y)
        ((Fintype.equivFin C).symm i) := by
  let e := Fintype.equivFin C
  let R := fun X : C ↦ representable (E := C) hC X
  let Rs := fun m : SmallIndex (C := C) ↦ representable (E := C) hC (e.symm m)
  apply biproduct.hom_ext'
  intro X
  by_cases hX : e X = i
  · have hXeq : X = e.symm i := by
      apply e.injective
      simpa using hX
    subst X
    simp only [generatorSmallIso, biproduct.ι_desc_assoc]
    rw [biproduct.eqToHom_comp_ι Rs (e.apply_symm_apply i).symm]
    rw [biproduct.ι_π_self, biproduct.ι_π_self]
  · have hX' : X ≠ e.symm i := by
      intro h
      apply hX
      rw [h, e.apply_symm_apply]
    simp [generatorSmallIso, R, Rs, e, hX, hX']

/-- Under the reindexing isomorphism, a small canonical projector is the
usual projector onto the corresponding summand. -/
theorem smallCanonicalProjector_eq_conjugate
    (i : SmallIndex (C := C)) :
    smallCanonicalProjector hC i =
      (generatorSmallIso hC).hom ≫
        (biproduct.π
            (fun j : SmallIndex (C := C) ↦
              representable (E := C) hC ((Fintype.equivFin C).symm j)) i ≫
          biproduct.ι
            (fun j : SmallIndex (C := C) ↦
              representable (E := C) hC ((Fintype.equivFin C).symm j)) i) ≫
        (generatorSmallIso hC).inv := by
  change _ = (generatorSmallIso hC).hom ≫ _ ≫ _ ≫
    (generatorSmallIso hC).inv
  simp only [← Category.assoc]
  rw [generatorSmallIso_hom_comp_π]
  simp [smallCanonicalProjector, generatorSmallIso, Category.assoc]

private def sourceSmallAlgebraEquiv :
    algebra hC ≃ₐ[k] End (sourceSmallGenerator hC) :=
  MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv
    (k := k) (generatorSmallIso hC)

private def mapSmallEnd (f : End (sourceSmallGenerator hC)) :
    mappedAlgebra hD F :=
  biproduct.matrix fun i j ↦
    mapRepresentableHom hC hD F
      ((Fintype.equivFin C).symm i) ((Fintype.equivFin C).symm j)
      (biproduct.components f i j)

private theorem small_components_comp
    (f g : End (sourceSmallGenerator hC))
    (i l : SmallIndex (C := C)) :
    biproduct.components (f ≫ g) i l =
      ∑ j : SmallIndex (C := C),
        biproduct.components f i j ≫ biproduct.components g j l := by
  classical
  let Q := fun i : SmallIndex (C := C) ↦
    representable (E := C) hC ((Fintype.equivFin C).symm i)
  unfold biproduct.components
  change (biproduct.ι Q i ≫ f) ≫ g ≫ biproduct.π Q l = _
  calc
    _ = biproduct.ι Q i ≫ f ≫ 𝟙 (⨁ Q) ≫
          g ≫ biproduct.π Q l := by
      have hid : f ≫ 𝟙 (⨁ Q) = f := Category.comp_id f
      have h := congrArg
        (fun q ↦ biproduct.ι Q i ≫ q ≫ g ≫ biproduct.π Q l) hid
      simpa only [Category.assoc] using h.symm
    _ = biproduct.ι Q i ≫ f ≫
          (∑ j, biproduct.π Q j ≫ biproduct.ι Q j) ≫
          g ≫ biproduct.π Q l := by rw [biproduct.total (f := Q)]
    _ = _ := by
      simpa only [Q, Preadditive.comp_sum, Preadditive.sum_comp,
        Category.assoc]

private theorem mapped_components_comp
    (f g : mappedAlgebra hD F)
    (i l : SmallIndex (C := C)) :
    biproduct.components (f ≫ g) i l =
      ∑ j : SmallIndex (C := C),
        biproduct.components f i j ≫ biproduct.components g j l := by
  classical
  let Q := fun i : SmallIndex (C := C) ↦
    representable (E := D) hD (F.obj ((Fintype.equivFin C).symm i))
  unfold biproduct.components
  change (biproduct.ι Q i ≫ f) ≫ g ≫ biproduct.π Q l = _
  calc
    _ = biproduct.ι Q i ≫ f ≫ 𝟙 (⨁ Q) ≫
          g ≫ biproduct.π Q l := by
      have hid : f ≫ 𝟙 (⨁ Q) = f := Category.comp_id f
      have h := congrArg
        (fun q ↦ biproduct.ι Q i ≫ q ≫ g ≫ biproduct.π Q l) hid
      simpa only [Category.assoc] using h.symm
    _ = biproduct.ι Q i ≫ f ≫
          (∑ j, biproduct.π Q j ≫ biproduct.ι Q j) ≫
          g ≫ biproduct.π Q l := by rw [biproduct.total (f := Q)]
    _ = _ := by
      simpa only [Q, Preadditive.comp_sum, Preadditive.sum_comp,
        Category.assoc]

private theorem source_components_add
    (f g : End (sourceSmallGenerator hC))
    (i j : SmallIndex (C := C)) :
    biproduct.components (f + g) i j =
      biproduct.components f i j + biproduct.components g i j := by
  unfold biproduct.components
  rw [Preadditive.add_comp, Preadditive.comp_add]

private theorem mapped_components_add
    (f g : mappedAlgebra hD F)
    (i j : SmallIndex (C := C)) :
    biproduct.components (f + g) i j =
      biproduct.components f i j + biproduct.components g i j := by
  unfold biproduct.components
  rw [Preadditive.add_comp, Preadditive.comp_add]

private theorem source_components_smul (c : k)
    (f : End (sourceSmallGenerator hC))
    (i j : SmallIndex (C := C)) :
    biproduct.components (c • f) i j =
      c • biproduct.components f i j := by
  unfold biproduct.components
  rw [Linear.smul_comp, Linear.comp_smul]

private theorem mapped_components_smul (c : k)
    (f : mappedAlgebra hD F)
    (i j : SmallIndex (C := C)) :
    biproduct.components (c • f) i j =
      c • biproduct.components f i j := by
  unfold biproduct.components
  rw [Linear.smul_comp, Linear.comp_smul]

private theorem mapSmallEnd_add (f g : End (sourceSmallGenerator hC)) :
    mapSmallEnd hC hD F (f + g) =
      mapSmallEnd hC hD F f + mapSmallEnd hC hD F g := by
  apply (biproduct.matrixEquiv).injective
  funext i j
  change biproduct.components (mapSmallEnd hC hD F (f + g)) i j =
    biproduct.components
      (mapSmallEnd hC hD F f + mapSmallEnd hC hD F g) i j
  rw [mapped_components_add]
  simp only [mapSmallEnd, biproduct.matrix_components]
  rw [source_components_add]
  rw [mapRepresentableHom_add]

private theorem mapSmallEnd_one :
    mapSmallEnd hC hD F 1 = 1 := by
  apply (biproduct.matrixEquiv).injective
  funext i j
  change biproduct.components (mapSmallEnd hC hD F 1) i j =
    biproduct.components (1 : mappedAlgebra hD F) i j
  simp only [mapSmallEnd, biproduct.matrix_components]
  by_cases hij : i = j
  · subst j
    rw [show biproduct.components (1 : End (sourceSmallGenerator hC)) i i =
        𝟙 _ by
      unfold biproduct.components
      simp]
    rw [mapRepresentableHom_id]
    unfold biproduct.components
    simp
  · rw [show biproduct.components (1 : End (sourceSmallGenerator hC)) i j =
        0 by
      unfold biproduct.components
      simp [hij]]
    rw [mapRepresentableHom_zero]
    unfold biproduct.components
    simp [hij]

private theorem mapSmallEnd_mul (f g : End (sourceSmallGenerator hC)) :
    mapSmallEnd hC hD F (f * g) =
      mapSmallEnd hC hD F f * mapSmallEnd hC hD F g := by
  classical
  apply (biproduct.matrixEquiv).injective
  funext i l
  change biproduct.components (mapSmallEnd hC hD F (g ≫ f)) i l =
    biproduct.components
      (mapSmallEnd hC hD F g ≫ mapSmallEnd hC hD F f) i l
  rw [mapped_components_comp hD F
    (mapSmallEnd hC hD F g) (mapSmallEnd hC hD F f) i l]
  simp only [mapSmallEnd, biproduct.matrix_components]
  rw [small_components_comp hC g f i l]
  induction (Finset.univ : Finset (SmallIndex (C := C))) using
      Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mapRepresentableHom_zero]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        mapRepresentableHom_add, ih]
      rw [mapRepresentableHom_comp]

private theorem mapSmallEnd_surjective [F.Full] :
    Function.Surjective (mapSmallEnd hC hD F) := by
  intro g
  let f : End (sourceSmallGenerator hC) :=
    biproduct.matrix fun i j ↦
      preimageRepresentableHom hC hD F
        ((Fintype.equivFin C).symm i) ((Fintype.equivFin C).symm j)
        (biproduct.components g i j)
  refine ⟨f, ?_⟩
  apply (biproduct.matrixEquiv).injective
  funext i j
  change biproduct.components (mapSmallEnd hC hD F f) i j =
    biproduct.components g i j
  simp only [mapSmallEnd, biproduct.matrix_components, f]
  exact mapRepresentableHom_preimage hC hD F _ _ _

private def mapSmallAlgHom :
    End (sourceSmallGenerator hC) →ₐ[k] mappedAlgebra hD F :=
  AlgHom.ofLinearMap
    { toFun := mapSmallEnd hC hD F
      map_add' := mapSmallEnd_add hC hD F
      map_smul' := by
        intro c f
        apply (biproduct.matrixEquiv).injective
        funext i j
        change biproduct.components (mapSmallEnd hC hD F (c • f)) i j =
          biproduct.components ((RingHom.id k) c • mapSmallEnd hC hD F f) i j
        rw [RingHom.id_apply, mapped_components_smul]
        simp only [mapSmallEnd, biproduct.matrix_components]
        rw [source_components_smul]
        rw [mapRepresentableHom_smul]
        }
    (mapSmallEnd_one hC hD F) (mapSmallEnd_mul hC hD F)

/-- The algebra homomorphism induced entrywise by a linear functor. -/
def mapAlgHom : algebra hC →ₐ[k] mappedAlgebra hD F :=
  (mapSmallAlgHom hC hD F).comp (sourceSmallAlgebraEquiv hC).toAlgHom

/-- A full linear functor induces a surjection onto the endomorphism algebra
of the source-indexed target generator. -/
theorem mapAlgHom_surjective [F.Full] :
    Function.Surjective (mapAlgHom hC hD F) := by
  intro g
  obtain ⟨f, hf⟩ := mapSmallEnd_surjective hC hD F g
  refine ⟨(sourceSmallAlgebraEquiv hC).symm f, ?_⟩
  change mapSmallEnd hC hD F
      ((sourceSmallAlgebraEquiv hC)
        ((sourceSmallAlgebraEquiv hC).symm f)) = g
  rw [(sourceSmallAlgebraEquiv hC).apply_symm_apply, hf]

private noncomputable def smallTargetObjectEquiv
    (hobj : Function.Bijective F.obj) : SmallIndex (C := C) ≃ D :=
  Equiv.ofBijective
    (fun i ↦ F.obj ((Fintype.equivFin C).symm i))
    (hobj.comp (Fintype.equivFin C).symm.bijective)

/-- If the functor is bijective on objects, its source-indexed sum of target
representables is the usual target projective generator. -/
def mappedGeneratorIsoOfBijective
    [Fintype D] (hobj : Function.Bijective F.obj) :
    mappedGenerator hD F ≅ finiteCategoryProjectiveGenerator hD :=
  biproduct.whiskerEquiv (smallTargetObjectEquiv F hobj)
    (fun _ ↦ Iso.refl _)

/-- The target-generator identification attached to an object-bijective
functor. -/
def mappedAlgebraEquivOfBijective
    [Fintype D] (hobj : Function.Bijective F.obj) :
    mappedAlgebra hD F ≃ₐ[k]
      finiteCategoryProjectiveGenerator.algebra hD :=
  MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv
    (k := k) (mappedGeneratorIsoOfBijective hD F hobj)

/-- The algebra homomorphism induced by a linear functor which is bijective
on objects, now with the usual target category algebra as codomain. -/
def mapAlgebraHomOfBijective
    [Fintype D] (hobj : Function.Bijective F.obj) :
    finiteCategoryProjectiveGenerator.algebra hC →ₐ[k]
      finiteCategoryProjectiveGenerator.algebra hD :=
  (mappedAlgebraEquivOfBijective hD F hobj).toAlgHom.comp
    (mapAlgHom hC hD F)

/-- A full, object-bijective linear functor induces a surjection of finite
category algebras. -/
theorem mapAlgebraHomOfBijective_surjective [F.Full]
    [Fintype D] (hobj : Function.Bijective F.obj) :
    Function.Surjective (mapAlgebraHomOfBijective hC hD F hobj) :=
  (mappedAlgebraEquivOfBijective hD F hobj).surjective.comp
    (mapAlgHom_surjective hC hD F)

/-- The category morphism in one reindexed matrix coordinate of a finite
category algebra element.  The orientation is reversed by covariant Yoneda:
the `(i,j)` map between representables is represented by a morphism from the
`j`-object to the `i`-object. -/
def smallAlgebraCategoryCoordinate
    (a : algebra hC) (i j : SmallIndex (C := C)) :
    (Fintype.equivFin C).symm j ⟶ (Fintype.equivFin C).symm i :=
  (biproduct.components (sourceSmallAlgebraEquiv hC a) i j).hom.hom.app
    ((Fintype.equivFin C).symm i) (𝟙 _)

theorem smallAlgebraCategoryCoordinate_smul
    (c : k) (a : algebra hC) (i j : SmallIndex (C := C)) :
    smallAlgebraCategoryCoordinate hC (c • a) i j =
      c • smallAlgebraCategoryCoordinate hC a i j := by
  unfold smallAlgebraCategoryCoordinate
  rw [map_smul, source_components_smul]
  rfl

/-- The category morphism in an object-indexed matrix coordinate of a finite
category algebra element.  As for the small reindexing above, covariant
Yoneda reverses the orientation of the displayed category morphism. -/
def algebraCategoryCoordinate
    (a : algebra hC) (X Y : C) : Y ⟶ X :=
  ((biproduct.ι (fun Z : C ↦ representable hC Z) X ≫ a ≫
      biproduct.π (fun Z : C ↦ representable hC Z) Y).hom.hom.app X)
    (𝟙 X)

/-- An element of a finite category algebra is determined by its
object-indexed category-morphism coordinates. -/
theorem algebraCategoryCoordinate_ext
    {a b : algebra hC}
    (h : ∀ X Y : C,
      algebraCategoryCoordinate hC a X Y =
        algebraCategoryCoordinate hC b X Y) :
    a = b := by
  apply End.ext
  apply biproduct.hom_ext'
  intro X
  apply biproduct.hom_ext
  intro Y
  apply ObjectProperty.hom_ext
  let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
    (Opposite.op Y)
  let f := (biproduct.ι (fun Z : C ↦
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
        (Opposite.op Z)) X ≫ a ≫
      biproduct.π (fun Z : C ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
          (Opposite.op Z)) Y).hom
  let g := (biproduct.ι (fun Z : C ↦
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
        (Opposite.op Z)) X ≫ b ≫
      biproduct.π (fun Z : C ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
          (Opposite.op Z)) Y).hom
  change f = g
  rw [← linearCoyonedaHom_self M.obj X f,
    ← linearCoyonedaHom_self M.obj X g]
  exact congrArg (linearCoyonedaHom M.obj X) (h X Y)

/-- Reindexing the finite projective generator does not change its category
morphism coordinates. -/
theorem smallAlgebraCategoryCoordinate_eq_algebraCategoryCoordinate
    (a : algebra hC) (i j : SmallIndex (C := C)) :
    smallAlgebraCategoryCoordinate hC a i j =
      algebraCategoryCoordinate hC a
        ((Fintype.equivFin C).symm i)
        ((Fintype.equivFin C).symm j) := by
  let e := Fintype.equivFin C
  let R := fun X : C ↦ representable hC X
  let Rs := fun m : SmallIndex (C := C) ↦ representable hC (e.symm m)
  have hι : biproduct.ι Rs i ≫ (generatorSmallIso hC).inv =
      biproduct.ι R (e.symm i) := by
    simp [generatorSmallIso, R, Rs, e]
  have hπ : (generatorSmallIso hC).hom ≫ biproduct.π Rs j =
      biproduct.π R (e.symm j) := by
    apply biproduct.hom_ext'
    intro X
    by_cases hX : e X = j
    · have hXeq : X = e.symm j := by
        apply e.injective
        simpa using hX
      subst X
      simp only [generatorSmallIso, biproduct.ι_desc_assoc]
      rw [biproduct.eqToHom_comp_ι Rs (e.apply_symm_apply j).symm]
      rw [biproduct.ι_π_self, biproduct.ι_π_self]
    · have hX' : X ≠ e.symm j := by
        intro h
        apply hX
        rw [h, e.apply_symm_apply]
      simp [generatorSmallIso, R, Rs, e, hX, hX']
  have hcoordinate :
      biproduct.ι Rs i ≫ (generatorSmallIso hC).inv ≫ a ≫
          (generatorSmallIso hC).hom ≫ biproduct.π Rs j =
        biproduct.ι R (e.symm i) ≫ a ≫
          biproduct.π R (e.symm j) := by
    calc
      _ = (biproduct.ι Rs i ≫ (generatorSmallIso hC).inv) ≫ a ≫
          ((generatorSmallIso hC).hom ≫ biproduct.π Rs j) := by
        simp only [Category.assoc]
      _ = _ := by rw [hι, hπ]
  unfold smallAlgebraCategoryCoordinate algebraCategoryCoordinate
  change
    (((biproduct.ι Rs i ≫ (generatorSmallIso hC).inv ≫ a ≫
        (generatorSmallIso hC).hom ≫ biproduct.π Rs j).hom.hom.app
      (e.symm i)) (𝟙 (e.symm i))) = _
  rw [hcoordinate]

/-- The functor-induced category-algebra map kills an element exactly when
the functor kills every one of its category-morphism matrix coordinates. -/
theorem mapAlgHom_eq_zero_iff_smallAlgebraCategoryCoordinate
    (a : algebra hC) :
    mapAlgHom hC hD F a = 0 ↔
      ∀ i j, F.map (smallAlgebraCategoryCoordinate hC a i j) = 0 := by
  change mapSmallEnd hC hD F (sourceSmallAlgebraEquiv hC a) = 0 ↔ _
  constructor
  · intro ha i j
    have hcomponent := congrArg
      (fun g : mappedAlgebra hD F ↦ biproduct.components g i j) ha
    have hzeroComponent :
        biproduct.components (0 : mappedAlgebra hD F) i j = 0 := by
      simp [biproduct.components]
    have hmapRepresentable :
        mapRepresentableHom hC hD F
          ((Fintype.equivFin C).symm i) ((Fintype.equivFin C).symm j)
          (biproduct.components (sourceSmallAlgebraEquiv hC a) i j) = 0 := by
      rw [hzeroComponent] at hcomponent
      simpa only [mapSmallEnd, biproduct.matrix_components] using hcomponent
    have happ := congrArg
      (fun q : representable (E := D) hD
            (F.obj ((Fintype.equivFin C).symm i)) ⟶
          representable (E := D) hD
            (F.obj ((Fintype.equivFin C).symm j)) ↦
        q.hom.hom.app (F.obj ((Fintype.equivFin C).symm i))
          (𝟙 _)) hmapRepresentable
    change
      (linearCoyonedaHom
        (representable (E := D) hD
          (F.obj ((Fintype.equivFin C).symm j))).obj
        (F.obj ((Fintype.equivFin C).symm i))
        (F.map (smallAlgebraCategoryCoordinate hC a i j))).hom.app
          (F.obj ((Fintype.equivFin C).symm i)) (𝟙 _) = 0 at happ
    rw [linearCoyonedaHom_app_id] at happ
    exact happ
  · intro ha
    apply (biproduct.matrixEquiv).injective
    funext i j
    have hentry :
        mapRepresentableHom hC hD F
          ((Fintype.equivFin C).symm i) ((Fintype.equivFin C).symm j)
          (biproduct.components (sourceSmallAlgebraEquiv hC a) i j) = 0 := by
      apply ObjectProperty.hom_ext
      change linearCoyonedaHom
          (representable (E := D) hD
            (F.obj ((Fintype.equivFin C).symm j))).obj
          (F.obj ((Fintype.equivFin C).symm i))
          (F.map (smallAlgebraCategoryCoordinate hC a i j)) = 0
      rw [ha i j]
      exact (linearCoyonedaHomEquiv
        (representable (E := D) hD
          (F.obj ((Fintype.equivFin C).symm j))).obj
        (F.obj ((Fintype.equivFin C).symm i))).symm.map_zero
    have hleft :
        biproduct.components
            (mapSmallEnd hC hD F (sourceSmallAlgebraEquiv hC a)) i j = 0 := by
      simpa only [mapSmallEnd, biproduct.matrix_components] using hentry
    have hright :
        biproduct.components (0 : mappedAlgebra hD F) i j = 0 := by
      simp [biproduct.components]
    exact hleft.trans hright.symm

/-- The same coordinatewise kernel criterion after identifying the
source-indexed target generator with the ordinary target generator. -/
theorem mapAlgebraHomOfBijective_eq_zero_iff_smallAlgebraCategoryCoordinate
    [Fintype D] (hobj : Function.Bijective F.obj) (a : algebra hC) :
    mapAlgebraHomOfBijective hC hD F hobj a = 0 ↔
      ∀ i j, F.map (smallAlgebraCategoryCoordinate hC a i j) = 0 := by
  rw [mapAlgebraHomOfBijective, AlgHom.comp_apply]
  constructor
  · intro ha
    apply (mapAlgHom_eq_zero_iff_smallAlgebraCategoryCoordinate
      hC hD F a).1
    exact (mappedAlgebraEquivOfBijective hD F hobj).injective
      (by simpa using ha)
  · intro ha
    have hzero :=
      (mapAlgHom_eq_zero_iff_smallAlgebraCategoryCoordinate
        hC hD F a).2 ha
    rw [hzero]
    exact map_zero _

/-- The object-indexed form of the coordinatewise kernel criterion. -/
theorem mapAlgebraHomOfBijective_eq_zero_iff_algebraCategoryCoordinate
    [Fintype D] (hobj : Function.Bijective F.obj) (a : algebra hC) :
    mapAlgebraHomOfBijective hC hD F hobj a = 0 ↔
      ∀ X Y : C, F.map (algebraCategoryCoordinate hC a X Y) = 0 := by
  rw [mapAlgebraHomOfBijective_eq_zero_iff_smallAlgebraCategoryCoordinate
    hC hD F hobj a]
  constructor
  · intro h X Y
    have hXY := h (Fintype.equivFin C X) (Fintype.equivFin C Y)
    rw [smallAlgebraCategoryCoordinate_eq_algebraCategoryCoordinate] at hXY
    rw [← (Fintype.equivFin C).symm_apply_apply X,
      ← (Fintype.equivFin C).symm_apply_apply Y]
    exact hXY
  · intro h i j
    rw [smallAlgebraCategoryCoordinate_eq_algebraCategoryCoordinate]
    exact h ((Fintype.equivFin C).symm i)
      ((Fintype.equivFin C).symm j)

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
