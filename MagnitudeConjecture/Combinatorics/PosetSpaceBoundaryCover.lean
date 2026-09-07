import MagnitudeConjecture.Combinatorics.PosetSpaceFullSupport

/-!
# Boundary-generator covers of finite poset spaces

Every finite poset space is a strict quotient of an explicit object assembled
from an empty-support ambient summand and principal-filter boundary summands.
The construction records the elementary projective presentation on the target
side of Iyama's realization.  The remaining algebraic issue is to lift this
strict quotient through the finite strict tau-category.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory

universe u

variable {k T : Type u} [Field k] [Fintype T] [PartialOrder T]

/-- The carrier of the boundary-generator cover.  The first coordinate is an
empty-support copy of the ambient space.  The second coordinate contains one
copy of `Y_t` for every boundary point `t`. -/
abbrev boundaryCoverCarrier (Y : Obj k T) :=
  Y × (∀ t : T, Y.subspace t)

/-- At `r`, the boundary cover retains exactly the coordinates indexed by
`t ≤ r`; the empty-support ambient coordinate is zero. -/
def boundaryCoverSubspace (Y : Obj k T) (r : T) :
    Submodule k (boundaryCoverCarrier Y) where
  carrier := {x | x.1 = 0 ∧ ∀ t : T, ¬ t ≤ r → x.2 t = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx₀, hx⟩ ⟨hy₀, hy⟩
    constructor
    · simp [hx₀, hy₀]
    · intro t htr
      simp [hx t htr, hy t htr]
  smul_mem' := by
    rintro a x ⟨hx₀, hx⟩
    constructor
    · simp [hx₀]
    · intro t htr
      simp [hx t htr]

/-- The explicit finite poset space built from the root and non-root boundary
coordinates. -/
def boundaryCover (Y : Obj k T) : Obj k T where
  carrier := boundaryCoverCarrier Y
  subspace := boundaryCoverSubspace Y
  monotone_subspace := by
    intro r s hrs x hx
    refine ⟨hx.1, ?_⟩
    intro t hts
    exact hx.2 t (fun htr ↦ hts (htr.trans hrs))

/-- Sum the ambient coordinate and all non-root boundary coordinates. -/
def boundaryCoverLinear (Y : Obj k T) :
    boundaryCoverCarrier Y →ₗ[k] Y where
  toFun x := x.1 + ∑ t : T, (x.2 t : Y)
  map_add' x y := by
    change (x.1 + y.1) + ∑ t : T, ((x.2 t + y.2 t : Y.subspace t) : Y) =
      (x.1 + ∑ t : T, (x.2 t : Y)) +
        (y.1 + ∑ t : T, (y.2 t : Y))
    simp only [Submodule.coe_add, Finset.sum_add_distrib]
    abel
  map_smul' a x := by
    change a • x.1 + ∑ t : T, ((a • x.2 t : Y.subspace t) : Y) =
      a • (x.1 + ∑ t : T, (x.2 t : Y))
    simp only [Submodule.coe_smul, Finset.smul_sum, smul_add]

/-- The canonical boundary-generator cover of `Y`. -/
def boundaryCoverMap (Y : Obj k T) : boundaryCover Y ⟶ Y where
  linear := boundaryCoverLinear Y
  map_subspace := by
    intro r x hx
    change x.1 + ∑ t : T, (x.2 t : Y) ∈ Y.subspace r
    rw [hx.1, zero_add]
    apply Submodule.sum_mem
    intro t _
    by_cases htr : t ≤ r
    · exact Y.monotone_subspace htr (x.2 t).2
    · rw [hx.2 t htr]
      exact (Y.subspace r).zero_mem

@[simp]
theorem boundaryCoverMap_linear (Y : Obj k T) :
    (boundaryCoverMap Y).linear = boundaryCoverLinear Y :=
  rfl

/-- The boundary cover is surjective on its ambient vector space. -/
theorem boundaryCoverMap_surjective (Y : Obj k T) :
    Function.Surjective (boundaryCoverMap Y).linear := by
  intro y
  refine ⟨(y, 0), ?_⟩
  change y + ∑ _t : T, (0 : Y) = y
  simp

/-- The canonical boundary cover is an epimorphism. -/
theorem boundaryCoverMap_epi (Y : Obj k T) : Epi (boundaryCoverMap Y) :=
  epi_of_linear_surjective (boundaryCoverMap Y)
    (boundaryCoverMap_surjective Y)

/-- The boundary cover is also surjective on every distinguished subspace.
Thus it is the strict/deflation-type cover used by the hereditary
torsionfree realization, not merely a categorical epimorphism. -/
theorem boundaryCoverMap_subspace_surjective
    (Y : Obj k T) (r : T) :
    Function.Surjective
      (((boundaryCoverMap Y).linear.domRestrict
        ((boundaryCover Y).subspace r)).codRestrict
          (Y.subspace r)
          (fun x ↦ (boundaryCoverMap Y).map_subspace r x.1 x.2)) := by
  classical
  intro y
  let coordinates : ∀ t : T, Y.subspace t := Pi.single r y
  let x : boundaryCoverCarrier Y := (0, coordinates)
  have hx : x ∈ (boundaryCover Y).subspace r := by
    constructor
    · rfl
    · intro t htr
      have hne : t ≠ r := fun h ↦ htr (h.le)
      simp [x, coordinates, Pi.single_eq_of_ne hne]
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change (0 : Y) + ∑ t : T, (coordinates t : Y) = y
  rw [zero_add, Finset.sum_eq_single r]
  · simp [coordinates]
  · intro t _ htr
    simp [coordinates, Pi.single_eq_of_ne htr]
  · simp

/-- Equivalently, the image of the `r`-subspace under the cover map is
exactly `Y_r`. -/
theorem map_boundaryCoverSubspace (Y : Obj k T) (r : T) :
    Submodule.map (boundaryCoverMap Y).linear
        ((boundaryCover Y).subspace r) =
      Y.subspace r := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (boundaryCoverMap Y).map_subspace r x hx
  · intro y hy
    obtain ⟨x, hx⟩ := boundaryCoverMap_subspace_surjective Y r ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

omit [Fintype T] in
/-- A morphism of poset spaces is boundary-surjective when it is surjective
on the ambient space and on each distinguished subspace. -/
def BoundarySurjective {X Y : Obj k T} (f : X ⟶ Y) : Prop :=
  Function.Surjective f.linear ∧
    ∀ r : T,
      Submodule.map f.linear (X.subspace r) = Y.subspace r

omit [Fintype T] in
/-- Boundary-surjective morphisms are closed under composition. -/
theorem BoundarySurjective.comp
    {X Y Z : Obj k T} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : BoundarySurjective f) (hg : BoundarySurjective g) :
    BoundarySurjective (f ≫ g) := by
  constructor
  · exact hg.1.comp hf.1
  · intro r
    rw [comp_linear, Submodule.map_comp f.linear g.linear,
      hf.2 r, hg.2 r]

omit [Fintype T] in
/-- Either direction of an isomorphism is boundary-surjective. -/
theorem boundarySurjective_iso_hom {X Y : Obj k T} (e : X ≅ Y) :
    BoundarySurjective e.hom := by
  constructor
  · intro y
    exact ⟨e.inv.linear y, by
      have h := congrArg Hom.linear e.inv_hom_id
      exact LinearMap.congr_fun h y⟩
  · intro r
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact e.hom.map_subspace r x hx
    · intro y hy
      refine ⟨e.inv.linear y, e.inv.map_subspace r y hy, ?_⟩
      have h := congrArg Hom.linear e.inv_hom_id
      exact LinearMap.congr_fun h y

/-- The canonical boundary cover is boundary-surjective. -/
theorem boundaryCoverMap_boundarySurjective (Y : Obj k T) :
    BoundarySurjective (boundaryCoverMap Y) :=
  ⟨boundaryCoverMap_surjective Y, map_boundaryCoverSubspace Y⟩

/-- The empty-support contribution of one ambient vector. -/
def boundaryCoverRootVector (Y : Obj k T) (y : Y) :
    boundaryCoverCarrier Y :=
  (y, 0)

/-- The principal-filter contribution of one vector in `Y_t`. -/
def boundaryCoverPointVector (Y : Obj k T) (t : T)
    (y : Y.subspace t) : boundaryCoverCarrier Y := by
  classical
  exact (0, Pi.single t y)

/-- The explicit cover is generated by its empty-support coordinate and its
principal-filter coordinates. -/
theorem boundaryCover_eq_root_add_sum_points
    (Y : Obj k T) (x : boundaryCoverCarrier Y) :
    x = boundaryCoverRootVector Y x.1 +
      ∑ t : T, boundaryCoverPointVector Y t (x.2 t) := by
  classical
  change x = (x.1, 0) + ∑ t : T, (0, Pi.single t (x.2 t))
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sum,
      Finset.sum_const_zero, add_zero]
  · simp only [Prod.snd_add, Prod.snd_sum]
    change x.2 =
      (0 : ∀ t : T, Y.subspace t) +
        ∑ t : T, Pi.single t (x.2 t)
    rw [zero_add]
    funext r
    rw [Finset.sum_apply, Finset.sum_eq_single r]
    · simp
    · intro t _ htr
      simp [Pi.single_eq_of_ne htr.symm]
    · simp

/-! ## Relative projectivity of the boundary lines -/

/-- A poset-space object is projective for boundary-surjective morphisms if
maps from it lift across every such morphism. -/
def BoundaryProjective (P : Obj k T) : Prop :=
  ∀ {X Y : Obj k T} (f : X ⟶ Y), BoundarySurjective f →
    ∀ g : P ⟶ Y, ∃ l : P ⟶ X, l ≫ f = g

/-- A vector lying in all subspaces on `U` defines a map from the line with
support `U`. -/
def lineMapOfVector
    (U : Set T) (hU : IsUpperSet U) (X : Obj k T) (x : X)
    (hx : ∀ r : T, r ∈ U → x ∈ X.subspace r) :
    line k T U hU ⟶ X where
  linear :=
    { toFun := fun a ↦ a • x
      map_add' := fun a b ↦ add_smul a b x
      map_smul' := fun a b ↦ by
        simp only [RingHom.id_apply]
        change (a * b) • x = a • (b • x)
        exact mul_smul a b x }
  map_subspace := by
    intro r a ha
    by_cases hr : r ∈ U
    · exact (X.subspace r).smul_mem a (hx r hr)
    · have ha₀ : a = 0 := by
        rw [line_subspace_of_not_mem k T U hU r hr] at ha
        simpa using ha
      subst a
      simp

omit [Fintype T] in
@[simp]
theorem lineMapOfVector_apply
    (U : Set T) (hU : IsUpperSet U) (X : Obj k T) (x : X)
    (hx : ∀ r : T, r ∈ U → x ∈ X.subspace r) (a : k) :
    (lineMapOfVector U hU X x hx).linear a = a • x :=
  rfl

/-- The empty upper support carried by the root boundary line. -/
abbrev emptySupport : Set T := ∅

omit [Fintype T] in
theorem emptySupport_isUpperSet : IsUpperSet (emptySupport : Set T) := by
  intro r _s _hrs hr
  exact False.elim hr

/-- The principal upper support carried by the boundary line at `t`. -/
def principalSupport (t : T) : Set T := {r | t ≤ r}

omit [Fintype T] in
theorem principalSupport_isUpperSet (t : T) :
    IsUpperSet (principalSupport t) := by
  intro r s hrs htr
  exact htr.trans hrs

omit [Fintype T] in
/-- The empty-support root line lifts across every boundary-surjective map. -/
theorem emptyLine_boundaryProjective :
    BoundaryProjective
      (line k T emptySupport emptySupport_isUpperSet) := by
  intro X Y f hf g
  obtain ⟨x, hx⟩ := hf.1 (g.linear 1)
  let l : line k T emptySupport emptySupport_isUpperSet ⟶ X :=
    lineMapOfVector emptySupport emptySupport_isUpperSet X x
      (fun _r hr ↦ False.elim hr)
  refine ⟨l, ?_⟩
  apply Hom.ext
  apply LinearMap.ext
  intro a
  change f.linear (a • x) = g.linear a
  rw [map_smul, hx]
  simpa using (g.linear.map_smul a (1 : k)).symm

omit [Fintype T] in
/-- Every principal-filter boundary line lifts across boundary-surjective
maps.  These are the non-root projectives of the exact boundary structure. -/
theorem principalLine_boundaryProjective (t : T) :
    BoundaryProjective
      (line k T (principalSupport t) (principalSupport_isUpperSet t)) := by
  intro X Y f hf g
  have hone : (1 : k) ∈
      (line k T (principalSupport t)
        (principalSupport_isUpperSet t)).subspace t := by
    rw [line_subspace_of_mem]
    · exact Submodule.mem_top
    · exact le_rfl
  have hgt : g.linear 1 ∈ Y.subspace t :=
    g.map_subspace t 1 hone
  have hgt' : g.linear 1 ∈
      Submodule.map f.linear (X.subspace t) := by
    rw [hf.2 t]
    exact hgt
  obtain ⟨x, hxt, hx⟩ := hgt'
  let l : line k T (principalSupport t)
      (principalSupport_isUpperSet t) ⟶ X :=
    lineMapOfVector (principalSupport t)
      (principalSupport_isUpperSet t) X x
      (fun r htr ↦ X.monotone_subspace htr hxt)
  refine ⟨l, ?_⟩
  apply Hom.ext
  apply LinearMap.ext
  intro a
  change f.linear (a • x) = g.linear a
  rw [map_smul, hx]
  simpa using (g.linear.map_smul a (1 : k)).symm

end MagnitudeConjecture.PosetSpace
