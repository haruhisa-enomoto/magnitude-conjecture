import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Fullness of an incidence representable functor

A morphism of represented poset spaces is a linear map on `Hom(P,-)` that
preserves the images of all `Hom(P_t,-)`.  When precomposition along
`P ⟶ P_t` is injective, it therefore lifts uniquely to every projective
coordinate.  If the chosen root maps span all maps from `P` to the boundary
projectives, these coordinate lifts commute with every boundary morphism and
assemble into a module map on the representable of the boundary biproduct.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.PosetSpace.RepresentableData

universe u v w z

variable {k T : Type u} {C : Type v} [Field k] [Fintype T] [PartialOrder T]
variable [Category.{u} C] [Preadditive C] [Linear k C]
  [HasFiniteBiproducts C]

/-- The usual finite-biproduct formula, with an index type in an arbitrary
universe.  Mathlib's existing statement currently fixes the index in
`Type 0`. -/
theorem biproduct_lift_eq_sum
    {J : Type w} [Fintype J] {F : J → C} [HasBiproduct F]
    {X : C} (g : ∀ j, X ⟶ F j) :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι F j := by
  classical
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π, Preadditive.sum_comp]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [biproduct.ι_π, hi]
  · simp

/-- Composition through a finite biproduct is the sum of the coordinate
composites, without a universe restriction on the index type. -/
theorem biproduct_lift_desc
    {J : Type w} [Fintype J] {F : J → C} [HasBiproduct F]
    {X Y : C} (g : ∀ j, X ⟶ F j) (h : ∀ j, F j ⟶ Y) :
    biproduct.lift g ≫ biproduct.desc h = ∑ j, g j ≫ h j := by
  rw [biproduct_lift_eq_sum g, Preadditive.sum_comp]
  simp

/-- Reindex a finite biproduct across index types in arbitrary universes. -/
noncomputable def biproductReindex
    {I : Type w} {J : Type z} [Finite I]
    (e : I ≃ J) (F : J → C)
    [HasBiproduct F] [HasBiproduct (fun i ↦ F (e i))] :
    (⨁ fun i ↦ F (e i)) ≅ ⨁ F where
  hom := biproduct.desc fun i ↦ biproduct.ι F (e i)
  inv := biproduct.lift fun i ↦ biproduct.π F (e i)
  hom_inv_id := by
    classical
    letI : Fintype I := Fintype.ofFinite I
    apply biproduct.hom_ext'
    intro i
    rw [Category.comp_id, ← Category.assoc, biproduct.ι_desc,
      biproduct_lift_eq_sum,
      Preadditive.comp_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi
      have he : e i ≠ e i' := fun heq ↦ hi (e.injective heq).symm
      simp only [← Category.assoc, biproduct.ι_π_ne F he, zero_comp]
    · simp
  inv_hom_id := by
    classical
    letI : Fintype I := Fintype.ofFinite I
    apply biproduct.hom_ext'
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have hrow : biproduct.ι F (e i) ≫
        biproduct.lift (fun i ↦ biproduct.π F (e i)) =
        biproduct.ι (fun i ↦ F (e i)) i := by
      rw [biproduct_lift_eq_sum, Preadditive.comp_sum]
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hi
        have he : e i ≠ e i' := fun heq ↦ hi (e.injective heq).symm
        simp only [← Category.assoc, biproduct.ι_π_ne F he, zero_comp]
      · simp
    rw [Category.comp_id, ← Category.assoc, hrow, biproduct.ι_desc]

/-- The root projective followed by the projectives indexed by the poset. -/
abbrev boundaryFamily (D : RepresentableData k T C) : Option T → C
  | none => D.source
  | some t => D.projective t

/-- The root identity and the chosen maps `P ⟶ P_t`, uniformly indexed. -/
def boundaryUnit (D : RepresentableData k T C) (q : Option T) :
    D.source ⟶ D.boundaryFamily q := by
  cases q with
  | none => exact 𝟙 D.source
  | some t => exact D.unit t

/-- Precomposition with a root-to-boundary map. -/
def boundaryPrecomposition (D : RepresentableData k T C)
    (q : Option T) (X : C) :
    (D.boundaryFamily q ⟶ X) →ₗ[k] (D.source ⟶ X) where
  toFun h := D.boundaryUnit q ≫ h
  map_add' h h' := by simp
  map_smul' c h := by simp

@[simp]
theorem boundaryPrecomposition_apply
    (D : RepresentableData k T C) (q : Option T) (X : C)
    (h : D.boundaryFamily q ⟶ X) :
    D.boundaryPrecomposition q X h = D.boundaryUnit q ≫ h :=
  rfl

/-- The biproduct of the root and all non-root boundary projectives. -/
abbrev boundaryGenerator (D : RepresentableData k T C) : C :=
  ⨁ D.boundaryFamily

theorem boundaryPrecomposition_injective
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (X : C),
      Function.Injective (D.precomposition t X))
    (q : Option T) (X : C) :
    Function.Injective (D.boundaryPrecomposition q X) := by
  cases q with
  | none =>
      intro h h' hEq
      rw [D.boundaryPrecomposition_apply,
        D.boundaryPrecomposition_apply] at hEq
      simpa [boundaryUnit] using hEq
  | some t =>
      change Function.Injective (D.precomposition t X)
      exact hinj t X

/-- A poset-space morphism sends the image of every boundary
precomposition map into the corresponding target image. -/
theorem map_boundaryPrecomposition_mem_range
    (D : RepresentableData k T C)
    {X Y : C} (f : D.obj X ⟶ D.obj Y)
    (q : Option T) (h : D.boundaryFamily q ⟶ X) :
    f.linear (D.boundaryPrecomposition q X h) ∈
      LinearMap.range (D.boundaryPrecomposition q Y) := by
  cases q with
  | none =>
      change D.source ⟶ X at h
      refine ⟨f.linear h, ?_⟩
      rw [D.boundaryPrecomposition_apply,
        D.boundaryPrecomposition_apply]
      simp [boundaryUnit]
  | some t =>
      exact f.map_subspace t _
        (show D.boundaryPrecomposition (some t) X h ∈
          (D.obj X).subspace t from ⟨h, rfl⟩)

/-- The map induced by a poset-space morphism on the ranges of the boundary
precomposition maps. -/
def boundaryRangeMap
    (D : RepresentableData k T C)
    {X Y : C} (f : D.obj X ⟶ D.obj Y) (q : Option T) :
    LinearMap.range (D.boundaryPrecomposition q X) →ₗ[k]
      LinearMap.range (D.boundaryPrecomposition q Y) where
  toFun x := ⟨f.linear x.1, by
    obtain ⟨h, hh⟩ := x.2
    rw [← hh]
    exact D.map_boundaryPrecomposition_mem_range f q h⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.linear.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact f.linear.map_smul c x.1

/-- The unique lift of a poset-space morphism to one boundary-projective
Hom coordinate. -/
def boundaryComponentMap
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    {X Y : C} (f : D.obj X ⟶ D.obj Y) (q : Option T) :
    (D.boundaryFamily q ⟶ X) →ₗ[k]
      (D.boundaryFamily q ⟶ Y) :=
  (LinearEquiv.ofInjective (D.boundaryPrecomposition q Y)
      (D.boundaryPrecomposition_injective hinj q Y)).symm.toLinearMap ∘ₗ
    D.boundaryRangeMap f q ∘ₗ
      (LinearEquiv.ofInjective (D.boundaryPrecomposition q X)
        (D.boundaryPrecomposition_injective hinj q X)).toLinearMap

@[simp]
theorem boundaryPrecomposition_componentMap
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    {X Y : C} (f : D.obj X ⟶ D.obj Y) (q : Option T)
    (h : D.boundaryFamily q ⟶ X) :
    D.boundaryPrecomposition q Y (D.boundaryComponentMap hinj f q h) =
      f.linear (D.boundaryPrecomposition q X h) := by
  change ((LinearEquiv.ofInjective (D.boundaryPrecomposition q Y)
      (D.boundaryPrecomposition_injective hinj q Y))
        ((LinearEquiv.ofInjective (D.boundaryPrecomposition q Y)
          (D.boundaryPrecomposition_injective hinj q Y)).symm
            (D.boundaryRangeMap f q
              ((LinearEquiv.ofInjective (D.boundaryPrecomposition q X)
                (D.boundaryPrecomposition_injective hinj q X)) h)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Coordinate lifts commute with every morphism among boundary
projectives.  The proof only uses that root-to-boundary maps span the
corresponding Hom spaces. -/
theorem boundaryComponentMap_natural
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    (hspan : ∀ (q : Option T)
      (a : D.source ⟶ D.boundaryFamily q),
      ∃ c : k, c • D.boundaryUnit q = a)
    {X Y : C} (f : D.obj X ⟶ D.obj Y)
    (q r : Option T) (a : D.boundaryFamily q ⟶ D.boundaryFamily r)
    (h : D.boundaryFamily r ⟶ X) :
    D.boundaryComponentMap hinj f q (a ≫ h) =
      a ≫ D.boundaryComponentMap hinj f r h := by
  apply D.boundaryPrecomposition_injective hinj q Y
  rw [D.boundaryPrecomposition_componentMap,
    show D.boundaryPrecomposition q Y
        (a ≫ D.boundaryComponentMap hinj f r h) =
      (D.boundaryUnit q ≫ a) ≫
        D.boundaryComponentMap hinj f r h by
      simp [boundaryPrecomposition, Category.assoc]]
  obtain ⟨c, hc⟩ := hspan r (D.boundaryUnit q ≫ a)
  calc
    f.linear (D.boundaryPrecomposition q X (a ≫ h)) =
        f.linear ((D.boundaryUnit q ≫ a) ≫ h) := by
      simp [boundaryPrecomposition, Category.assoc]
    _ = f.linear ((c • D.boundaryUnit r) ≫ h) := by rw [hc]
    _ = f.linear (c • (D.boundaryUnit r ≫ h)) := by simp
    _ = c • f.linear (D.boundaryUnit r ≫ h) := f.linear.map_smul _ _
    _ = c • D.boundaryPrecomposition r Y
        (D.boundaryComponentMap hinj f r h) := by
      congr 1
      exact (D.boundaryPrecomposition_componentMap hinj f r h).symm
    _ = (c • D.boundaryUnit r) ≫
        D.boundaryComponentMap hinj f r h := by
      rw [D.boundaryPrecomposition_apply, Linear.smul_comp]
    _ = (D.boundaryUnit q ≫ a) ≫
        D.boundaryComponentMap hinj f r h := by rw [hc]

/-- The coordinate lifts assembled on the boundary biproduct. -/
def boundaryTotalLinearMap
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    {X Y : C} (f : D.obj X ⟶ D.obj Y) :
    (D.boundaryGenerator ⟶ X) →ₗ[k] (D.boundaryGenerator ⟶ Y) where
  toFun h := biproduct.desc fun q ↦
    D.boundaryComponentMap hinj f q
      (biproduct.ι D.boundaryFamily q ≫ h)
  map_add' h h' := by
    apply biproduct.hom_ext'
    intro q
    simp only [biproduct.ι_desc, Preadditive.comp_add,
      LinearMap.map_add]
  map_smul' c h := by
    apply biproduct.hom_ext'
    intro q
    simpa only [biproduct.ι_desc, Linear.comp_smul,
      LinearMap.map_smul, RingHom.id_apply]

@[simp]
theorem boundary_ι_totalLinearMap
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    {X Y : C} (f : D.obj X ⟶ D.obj Y)
    (q : Option T) (h : D.boundaryGenerator ⟶ X) :
    biproduct.ι D.boundaryFamily q ≫ D.boundaryTotalLinearMap hinj f h =
      D.boundaryComponentMap hinj f q
        (biproduct.ι D.boundaryFamily q ≫ h) := by
  exact biproduct.ι_desc _ _

/-- The assembled map is natural for precomposition by every endomorphism
of the boundary generator. -/
theorem boundaryTotalLinearMap_natural
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    (hspan : ∀ (q : Option T)
      (a : D.source ⟶ D.boundaryFamily q),
      ∃ c : k, c • D.boundaryUnit q = a)
    {X Y : C} (f : D.obj X ⟶ D.obj Y)
    (a : D.boundaryGenerator ⟶ D.boundaryGenerator)
    (h : D.boundaryGenerator ⟶ X) :
    D.boundaryTotalLinearMap hinj f (a ≫ h) =
      a ≫ D.boundaryTotalLinearMap hinj f h := by
  classical
  apply biproduct.hom_ext'
  intro q
  let m : ∀ r : Option T,
      D.boundaryFamily q ⟶ D.boundaryFamily r := fun r ↦
    biproduct.ι D.boundaryFamily q ≫ a ≫
      biproduct.π D.boundaryFamily r
  have ha : biproduct.ι D.boundaryFamily q ≫ a =
      biproduct.lift m := by
    apply biproduct.hom_ext
    intro r
    simp only [biproduct.lift_π, m, Category.assoc]
  have hh : h = biproduct.desc fun r ↦
      biproduct.ι D.boundaryFamily r ≫ h := by
    apply biproduct.hom_ext'
    intro r
    simp
  rw [D.boundary_ι_totalLinearMap]
  simp only [← Category.assoc]
  rw [ha]
  have hlift_h : biproduct.lift m ≫ h =
      biproduct.lift m ≫ biproduct.desc (fun r ↦
        biproduct.ι D.boundaryFamily r ≫ h) :=
    congrArg (fun z ↦ biproduct.lift m ≫ z) hh
  rw [hlift_h]
  have hleft : biproduct.lift m ≫ biproduct.desc (fun r ↦
      biproduct.ι D.boundaryFamily r ≫ h) =
      ∑ r, m r ≫ (biproduct.ι D.boundaryFamily r ≫ h) :=
    biproduct_lift_desc m _
  rw [hleft, map_sum]
  change (∑ r, D.boundaryComponentMap hinj f q
      (m r ≫ (biproduct.ι D.boundaryFamily r ≫ h))) =
    biproduct.lift m ≫ biproduct.desc (fun r ↦
      D.boundaryComponentMap hinj f r
        (biproduct.ι D.boundaryFamily r ≫ h))
  rw [biproduct_lift_desc]
  apply Finset.sum_congr rfl
  intro r _
  exact D.boundaryComponentMap_natural hinj hspan f q r (m r)
    (biproduct.ι D.boundaryFamily r ≫ h)

/-- A poset-space morphism determines a module morphism between the
representables of the boundary generator. -/
def boundaryModuleMap
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    (hspan : ∀ (q : Option T)
      (a : D.source ⟶ D.boundaryFamily q),
      ∃ c : k, c • D.boundaryUnit q = a)
    {X Y : C} (f : D.obj X ⟶ D.obj Y) :
    (preadditiveCoyonedaObj D.boundaryGenerator).obj X ⟶
      (preadditiveCoyonedaObj D.boundaryGenerator).obj Y :=
  ModuleCat.ofHom
    { toFun := D.boundaryTotalLinearMap hinj f
      map_add' := (D.boundaryTotalLinearMap hinj f).map_add
      map_smul' := fun a h ↦ by
        change D.boundaryTotalLinearMap hinj f (a.unop ≫ h) =
          a.unop ≫ D.boundaryTotalLinearMap hinj f h
        exact D.boundaryTotalLinearMap_natural hinj hspan f a.unop h }

/-- Fullness of restricted Yoneda on the boundary generator implies
fullness of the concrete represented poset-space functor. -/
theorem map_surjective_of_boundaryCoyoneda_full
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (Z : C),
      Function.Injective (D.precomposition t Z))
    (hspan : ∀ (q : Option T)
      (a : D.source ⟶ D.boundaryFamily q),
      ∃ c : k, c • D.boundaryUnit q = a)
    (hfull : (preadditiveCoyonedaObj D.boundaryGenerator).Full)
    {X Y : C} (f : D.obj X ⟶ D.obj Y) :
    ∃ g : X ⟶ Y, D.map g = f := by
  obtain ⟨g, hg⟩ := hfull.map_surjective
    (D.boundaryModuleMap hinj hspan f)
  refine ⟨g, ?_⟩
  apply Hom.ext
  apply LinearMap.ext
  intro h
  have happ := congrArg
    (fun q ↦ q.hom (biproduct.π D.boundaryFamily none ≫ h)) hg
  have hroot := congrArg
    (fun q ↦ biproduct.ι D.boundaryFamily none ≫ q) happ
  change h ≫ g = f.linear h
  change biproduct.ι D.boundaryFamily none ≫
      ((biproduct.π D.boundaryFamily none ≫ h) ≫ g) =
    biproduct.ι D.boundaryFamily none ≫
      D.boundaryTotalLinearMap hinj f
        (biproduct.π D.boundaryFamily none ≫ h) at hroot
  rw [D.boundary_ι_totalLinearMap] at hroot
  have hroot' : h ≫ g = D.boundaryComponentMap hinj f none h := by
    simpa [Category.assoc] using hroot
  rw [hroot']
  have hc := D.boundaryPrecomposition_componentMap hinj f none h
  simpa [boundaryUnit, boundaryPrecomposition] using hc

end MagnitudeConjecture.PosetSpace.RepresentableData
