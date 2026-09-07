import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction
import MagnitudeConjecture.CategoryTheory.OrbitPushdownDescent
import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton

/-!
# The universal mesh category as a deck orbit

The universal translation-quiver projection is invariant under its deck
group.  This file descends the induced raw mesh functor through the coherent
shift-orbit category and identifies the resulting orbit category with the
downstairs raw mesh category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe u v w

variable {Q : Type v} [Quiver.{w} Q]

/-- The canonical arrow-star finiteness on the universal cover, transported
from the downstairs quiver covering. -/
noncomputable instance vertexStarFintype (T : RightMeshData Q) (x₀ : Q)
    [∀ y : Q, Fintype (Quiver.Star y)]
    (W : Vertex T x₀) : Fintype (Quiver.Star W) :=
  (cover T x₀).sourceStarFintype W

/-- The universal-cover projection on raw mesh categories, with the canonical
source arrow-star finiteness retained literally. -/
noncomputable def meshProjectionFunctor (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    RawCategory (k := k) (rightMeshData T x₀) ⥤ RawCategory (k := k) T :=
  (cover T x₀).functorUsingSourceFintype (k := k)

noncomputable instance meshProjectionFunctor_additive
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    (meshProjectionFunctor T x₀ (k := k)).Additive := by
  dsimp only [meshProjectionFunctor]
  infer_instance

noncomputable instance meshProjectionFunctor_linear
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    (meshProjectionFunctor T x₀ (k := k)).Linear k := by
  dsimp only [meshProjectionFunctor]
  infer_instance

/-- The raw mesh projection remains a Bongartz--Gabriel linear covering. -/
theorem meshProjectionFunctor_isCovering
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (meshProjectionFunctor T x₀ (k := k)) := by
  exact (cover T x₀).functorUsingSourceFintype_isCovering (k := k)

/-- Deck translation is invisible on projected raw-mesh objects. -/
@[simp]
theorem meshProjectionFunctor_obj_deckMeshEndofunctor
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (meshProjectionFunctor T x₀ (k := k)).obj
        ((deckMeshEndofunctor T x₀ g (k := k)).obj X) =
      (meshProjectionFunctor T x₀ (k := k)).obj X := by
  rcases X with ⟨X⟩
  change
    (meshProjectionFunctor T x₀ (k := k)).obj
        ((deckMeshEndofunctor T x₀ g (k := k)).obj
          (obj (k := k) (rightMeshData T x₀)
            (MagnitudeConjecture.LinearPathCategory.vertex X))) = _
  rw [deckMeshEndofunctor_obj_obj]
  unfold meshProjectionFunctor
  rw [(cover T x₀).functorUsingSourceFintype_obj_obj]
  change obj (k := k) T
      ((g • MagnitudeConjecture.LinearPathCategory.vertex X).1) =
    obj (k := k) T (MagnitudeConjecture.LinearPathCategory.vertex X).1
  rfl

/-- Two universal raw-mesh objects in the same projection fibre differ by a
unique deck transformation. -/
theorem existsUnique_deckMeshEndofunctor_obj_eq_of_projection_eq
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (Y Z : RawCategory (k := k) (rightMeshData T x₀))
    (hYZ : (meshProjectionFunctor T x₀ (k := k)).obj Z =
      (meshProjectionFunctor T x₀ (k := k)).obj Y) :
    ∃! g : FundamentalGroup T x₀,
      (deckMeshEndofunctor T x₀ g (k := k)).obj Y = Z := by
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  let WY := MagnitudeConjecture.LinearPathCategory.vertex Y
  let WZ := MagnitudeConjecture.LinearPathCategory.vertex Z
  have hvertex : WZ.1 = WY.1 := by
    change
      (meshProjectionFunctor T x₀ (k := k)).obj
          (obj (k := k) (rightMeshData T x₀) WZ) =
        (meshProjectionFunctor T x₀ (k := k)).obj
          (obj (k := k) (rightMeshData T x₀) WY) at hYZ
    unfold meshProjectionFunctor at hYZ
    rw [(cover T x₀).functorUsingSourceFintype_obj_obj,
      (cover T x₀).functorUsingSourceFintype_obj_obj] at hYZ
    have hfree := congrArg CategoryTheory.Quotient.as hYZ
    exact congrArg MagnitudeConjecture.LinearPathCategory.vertex hfree
  obtain ⟨g, hg⟩ := exists_smul_eq_of_vertex_eq T x₀ WY WZ hvertex.symm
  refine ⟨g, ?_, ?_⟩
  · change
      (deckMeshEndofunctor T x₀ g (k := k)).obj
          (obj (k := k) (rightMeshData T x₀) WY) =
        obj (k := k) (rightMeshData T x₀) WZ
    rw [deckMeshEndofunctor_obj_obj, hg]
  · intro h hh
    apply deck_smul_injective T x₀ WY
    have heq := congrArg CategoryTheory.Quotient.as hh
    change h • WY = WZ at heq
    exact heq.trans hg.symm

/-- At a fixed universal raw-mesh object, the deck-transformation object map
is injective in the deck transformation. -/
theorem deckMeshEndofunctor_obj_injective_in_group
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (Y : RawCategory (k := k) (rightMeshData T x₀)) :
    Function.Injective (fun g : FundamentalGroup T x₀ ↦
      (deckMeshEndofunctor T x₀ g (k := k)).obj Y) := by
  intro g h hgh
  rcases Y with ⟨Y⟩
  let WY := MagnitudeConjecture.LinearPathCategory.vertex Y
  apply deck_smul_injective T x₀ WY
  have heq := congrArg CategoryTheory.Quotient.as hgh
  change g • WY = h • WY at heq
  exact heq

/-- Additive deck-shift degrees parametrize the target fibre of the universal
raw-mesh projection.  The inverse appears because right shifts are defined
from the inverse left deck action. -/
noncomputable def deckShiftTargetFiberEquiv
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (Y : RawCategory (k := k) (rightMeshData T x₀)) :
    Additive (FundamentalGroup T x₀) ≃
      MagnitudeConjecture.LinearCovering.Fiber
        (meshProjectionFunctor T x₀ (k := k))
        ((meshProjectionFunctor T x₀ (k := k)).obj Y) :=
  Equiv.ofBijective
    (fun a ↦
      ⟨(deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).obj Y,
        meshProjectionFunctor_obj_deckMeshEndofunctor
          T x₀ a.toMul⁻¹ (k := k) Y⟩)
    (by
      constructor
      · intro a b hab
        change a.toMul = b.toMul
        apply inv_injective
        apply deckMeshEndofunctor_obj_injective_in_group
          T x₀ (k := k) Y
        exact congrArg Subtype.val hab
      · intro Z
        obtain ⟨g, hg, _⟩ :=
          existsUnique_deckMeshEndofunctor_obj_eq_of_projection_eq
            T x₀ (k := k) Y Z.1 Z.2
        refine ⟨Additive.ofMul g⁻¹, ?_⟩
        apply Subtype.ext
        change
          (deckMeshEndofunctor T x₀ (g⁻¹)⁻¹ (k := k)).obj Y = Z.1
        simpa using hg)

/-- Projecting a deck-translated path forgets exactly the deck translation. -/
theorem projection_mapPath_deckPrefunctor
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {W Z : Vertex T x₀} (p : Quiver.Path W Z) :
    (projection T x₀).mapPath ((deckPrefunctor T x₀ g).mapPath p) =
      (projection T x₀).mapPath p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons,
        Prefunctor.mapPath_cons, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The raw mesh projection is unchanged after any deck endofunctor. -/
theorem meshProjectionFunctor_map_deckMeshEndofunctor
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    {X Y : RawCategory (k := k) (rightMeshData T x₀)} (f : X ⟶ Y) :
    (meshProjectionFunctor T x₀ (k := k)).map
        ((deckMeshEndofunctor T x₀ g (k := k)).map f) =
      (meshProjectionFunctor T x₀ (k := k)).map f := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  induction f using Quot.inductionOn with
  | _ f =>
      let lhs : (X ⟶ Y) →ₗ[k]
          ((meshProjectionFunctor T x₀ (k := k)).obj
              ((deckMeshEndofunctor T x₀ g (k := k)).obj ⟨X⟩) ⟶
            (meshProjectionFunctor T x₀ (k := k)).obj
              ((deckMeshEndofunctor T x₀ g (k := k)).obj ⟨Y⟩)) :=
        { toFun := fun a ↦
            (meshProjectionFunctor T x₀ (k := k)).map
              ((deckMeshEndofunctor T x₀ g (k := k)).map
                ((quotientFunctor (k := k) (rightMeshData T x₀)).map a))
          map_add' := by
            intro a b
            rw [(quotientFunctor (k := k)
                (rightMeshData T x₀)).map_add,
              (deckMeshEndofunctor T x₀ g (k := k)).map_add,
              (meshProjectionFunctor T x₀ (k := k)).map_add]
          map_smul' := by
            intro r a
            rw [(quotientFunctor (k := k)
                (rightMeshData T x₀)).map_smul,
              (deckMeshEndofunctor T x₀ g (k := k)).map_smul,
              (meshProjectionFunctor T x₀ (k := k)).map_smul]
            simp only [RingHom.id_apply] }
      let rhs : (X ⟶ Y) →ₗ[k]
          ((meshProjectionFunctor T x₀ (k := k)).obj ⟨X⟩ ⟶
            (meshProjectionFunctor T x₀ (k := k)).obj ⟨Y⟩) :=
        { toFun := fun a ↦
            (meshProjectionFunctor T x₀ (k := k)).map
              ((quotientFunctor (k := k) (rightMeshData T x₀)).map a)
          map_add' := by
            intro a b
            rw [(quotientFunctor (k := k)
                (rightMeshData T x₀)).map_add,
              (meshProjectionFunctor T x₀ (k := k)).map_add]
          map_smul' := by
            intro r a
            rw [(quotientFunctor (k := k)
                (rightMeshData T x₀)).map_smul,
              (meshProjectionFunctor T x₀ (k := k)).map_smul]
            simp only [RingHom.id_apply] }
      change lhs f = rhs f
      have hlr : lhs = rhs := by
        apply (MagnitudeConjecture.LinearPathCategory.homPathBasis X Y).ext
        intro p
        dsimp only [lhs, rhs]
        simp only [MagnitudeConjecture.LinearPathCategory.homPathBasis_apply]
        change
          (meshProjectionFunctor T x₀ (k := k)).map
              ((deckMeshEndofunctor T x₀ g (k := k)).map
                ((quotientFunctor (k := k) (rightMeshData T x₀)).map
                  (MagnitudeConjecture.LinearPathCategory.pathHom p))) =
            (meshProjectionFunctor T x₀ (k := k)).map
              ((quotientFunctor (k := k) (rightMeshData T x₀)).map
                (MagnitudeConjecture.LinearPathCategory.pathHom p))
        unfold deckMeshEndofunctor meshProjectionFunctor
        rw [(deckCover T x₀ g).functorUsingSourceFintype_map_quotient_pathHom,
          (cover T x₀).functorUsingSourceFintype_map_quotient_pathHom,
          (cover T x₀).functorUsingSourceFintype_map_quotient_pathHom]
        apply congrArg (quotientFunctor (k := k) T).map
        apply congrArg MagnitudeConjecture.LinearPathCategory.pathHom
        exact projection_mapPath_deckPrefunctor T x₀ g p
      exact LinearMap.congr_fun hlr f

/-- Deck translation followed by projection is naturally the projection. -/
noncomputable def deckMeshProjectionIso
    (T : RightMeshData Q) (x₀ : Q) (g : FundamentalGroup T x₀)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    deckMeshEndofunctor T x₀ g (k := k) ⋙
        meshProjectionFunctor T x₀ (k := k) ≅
      meshProjectionFunctor T x₀ (k := k) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by
      intro X Y f
      change
        (meshProjectionFunctor T x₀ (k := k)).map
              ((deckMeshEndofunctor T x₀ g (k := k)).map f) ≫ 𝟙 _ =
          𝟙 _ ≫ (meshProjectionFunctor T x₀ (k := k)).map f
      rw [Category.comp_id, Category.id_comp]
      exact meshProjectionFunctor_map_deckMeshEndofunctor
        T x₀ g (k := k) f)

/-- Projection sends the identity-deck comparison to an identity morphism. -/
theorem meshProjectionFunctor_map_deckMeshEndofunctorOneIso_hom_app
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (meshProjectionFunctor T x₀ (k := k)).map
        ((deckMeshEndofunctorOneIso T x₀ (k := k)).hom.app X) =
      𝟙 ((meshProjectionFunctor T x₀ (k := k)).obj X) := by
  simp only [deckMeshEndofunctorOneIso, NatIso.ofComponents_hom_app]
  change (meshProjectionFunctor T x₀ (k := k)).map
      (eqToHom (deckMeshEndofunctor_one_obj T x₀ (k := k) X)) = _
  rw [eqToHom_map]
  apply eq_of_heq
  exact eqToHom_heq_id_dom _ _ _

/-- Projection sends the product-deck comparison to an identity morphism. -/
theorem meshProjectionFunctor_map_deckMeshEndofunctorMulIso_hom_app
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (g h : FundamentalGroup T x₀)
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (meshProjectionFunctor T x₀ (k := k)).map
        ((deckMeshEndofunctorMulIso T x₀ (k := k) g h).hom.app X) =
      𝟙 ((meshProjectionFunctor T x₀ (k := k)).obj X) := by
  simp only [deckMeshEndofunctorMulIso, NatIso.ofComponents_hom_app]
  change (meshProjectionFunctor T x₀ (k := k)).map
      (eqToHom (deckMeshEndofunctor_mul_obj T x₀ (k := k) g h X)) = _
  rw [eqToHom_map]
  apply eq_of_heq
  exact eqToHom_heq_id_dom _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Projection kills the unit comparison in the deck shift core. -/
theorem meshProjectionFunctor_map_deckMeshShiftCore_zero_hom_app
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (meshProjectionFunctor T x₀ (k := k)).map
        ((deckMeshShiftCore T x₀ (k := k)).zero.hom.app X) =
      𝟙 ((meshProjectionFunctor T x₀ (k := k)).obj X) := by
  apply eq_of_heq
  unfold deckMeshShiftCore
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [(meshProjectionFunctor T x₀ (k := k)).map_comp]
  simp only [deckMeshEndofunctorOneIso,
    NatIso.ofComponents_hom_app, eqToIso.hom, eqToHom_app]
  rw [eqToHom_map, eqToHom_map]
  exact HEq.trans (comp_eqToHom_heq _ _)
    (eqToHom_heq_id_dom _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Projection kills every addition comparison in the deck shift core. -/
theorem meshProjectionFunctor_map_deckMeshShiftCore_add_hom_app
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (a b : Additive (FundamentalGroup T x₀))
    (X : RawCategory (k := k) (rightMeshData T x₀)) :
    (meshProjectionFunctor T x₀ (k := k)).map
        ((deckMeshShiftCore T x₀ (k := k)).add a b |>.hom.app X) =
      𝟙 ((meshProjectionFunctor T x₀ (k := k)).obj X) := by
  apply eq_of_heq
  unfold deckMeshShiftCore
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [(meshProjectionFunctor T x₀ (k := k)).map_comp]
  simp only [deckMeshEndofunctorMulIso,
    NatIso.ofComponents_hom_app, eqToIso.hom, eqToHom_app]
  rw [eqToHom_map, eqToHom_map]
  exact HEq.trans (comp_eqToHom_heq _ _)
    (eqToHom_heq_id_dom _ _ _)

noncomputable instance deckMeshCoherentDeckShift_core_additive
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (a : Additive (FundamentalGroup T x₀)) :
    ((deckMeshCoherentDeckShift T x₀ (k := k)).core.F a).Additive := by
  change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Additive
  infer_instance

noncomputable instance deckMeshCoherentDeckShift_core_linear
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (a : Additive (FundamentalGroup T x₀)) :
    ((deckMeshCoherentDeckShift T x₀ (k := k)).core.F a).Linear k := by
  change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Linear k
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The raw mesh projection commutes coherently with deck shifts when the
downstairs category is given the trivial shift. -/
@[implicit_reducible]
noncomputable def meshProjectionCommShift
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI : HasShift (RawCategory (k := k) T)
        (Additive (FundamentalGroup T x₀)) :=
      MagnitudeConjecture.CoveringHom.trivialHasShift _ _
    (meshProjectionFunctor T x₀ (k := k)).CommShift
      (Additive (FundamentalGroup T x₀)) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI : HasShift (RawCategory (k := k) T)
      (Additive (FundamentalGroup T x₀)) :=
    MagnitudeConjecture.CoveringHom.trivialHasShift _ _
  let P := meshProjectionFunctor T x₀ (k := k)
  refine
    { commShiftIso := fun a ↦
        deckMeshProjectionIso T x₀ a.toMul⁻¹ (k := k) ≪≫
          (Functor.rightUnitor P).symm
      commShiftIso_zero := ?_
      commShiftIso_add := ?_ }
  · apply Iso.ext
    apply NatTrans.ext
    funext X
    apply eq_of_heq
    simp only [Functor.CommShift.isoZero_hom_app]
    rw [D.core.shiftFunctorZero_eq,
      (MagnitudeConjecture.CoveringHom.trivialShiftMkCore
        (RawCategory (k := k) T)
        (Additive (FundamentalGroup T x₀))).shiftFunctorZero_eq]
    simp [D, deckMeshCoherentDeckShift, deckMeshProjectionIso,
      MagnitudeConjecture.CoveringHom.trivialShiftMkCore,
      meshProjectionFunctor_map_deckMeshShiftCore_zero_hom_app]
    unfold deckMeshEndofunctor meshProjectionFunctor
    rfl
  · intro a b
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply eq_of_heq
    simp only [Functor.CommShift.isoAdd_hom_app]
    rw [D.core.shiftFunctorAdd_eq,
      (MagnitudeConjecture.CoveringHom.trivialShiftMkCore
        (RawCategory (k := k) T)
        (Additive (FundamentalGroup T x₀))).shiftFunctorAdd_eq]
    simp [D, deckMeshCoherentDeckShift, deckMeshProjectionIso,
      MagnitudeConjecture.CoveringHom.trivialShiftMkCore,
      meshProjectionFunctor_map_deckMeshShiftCore_add_hom_app]
    unfold deckMeshEndofunctor meshProjectionFunctor
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The commutation isomorphism is precisely the equality transport supplied
by the corresponding point of the projection fibre. -/
theorem meshProjectionCommShift_hom_app
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (a : Additive (FundamentalGroup T x₀))
    (Y : RawCategory (k := k) (rightMeshData T x₀)) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI : HasShift (RawCategory (k := k) T)
        (Additive (FundamentalGroup T x₀)) :=
      MagnitudeConjecture.CoveringHom.trivialHasShift _ _
    letI := meshProjectionCommShift T x₀ (k := k)
    ((meshProjectionFunctor T x₀ (k := k)).commShiftIso a).hom.app Y =
      eqToHom (meshProjectionFunctor_obj_deckMeshEndofunctor
        T x₀ a.toMul⁻¹ (k := k) Y) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI : HasShift (RawCategory (k := k) T)
      (Additive (FundamentalGroup T x₀)) :=
    MagnitudeConjecture.CoveringHom.trivialHasShift _ _
  letI := meshProjectionCommShift T x₀ (k := k)
  apply eq_of_heq
  unfold Functor.commShiftIso
  simp [meshProjectionCommShift, deckMeshProjectionIso]

/-- The descended universal mesh projection from the concrete shift-orbit
category. -/
noncomputable def meshShiftOrbitProjectionFunctor
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    MagnitudeConjecture.CoveringHom.ShiftOrbitCategory
        (RawCategory (k := k) (rightMeshData T x₀))
        (Additive (FundamentalGroup T x₀)) ⥤
      RawCategory (k := k) T := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI (a : Additive (FundamentalGroup T x₀)) :
      (D.core.F a).Additive := by
    change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Additive
    infer_instance
  letI (a : Additive (FundamentalGroup T x₀)) :
      (D.core.F a).Linear k := by
    change (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).Linear k
    infer_instance
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : HasShift (RawCategory (k := k) T)
      (Additive (FundamentalGroup T x₀)) :=
    MagnitudeConjecture.CoveringHom.trivialHasShift _ _
  letI := meshProjectionCommShift T x₀ (k := k)
  exact MagnitudeConjecture.CoveringHom.shiftOrbitDescendedFunctor
    (k := k) (A := Additive (FundamentalGroup T x₀))
      (meshProjectionFunctor T x₀ (k := k))

noncomputable instance meshShiftOrbitProjectionFunctor_additive
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    (meshShiftOrbitProjectionFunctor T x₀ (k := k)).Additive := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  dsimp only [meshShiftOrbitProjectionFunctor]
  infer_instance

noncomputable instance meshShiftOrbitProjectionFunctor_linear
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (meshShiftOrbitProjectionFunctor T x₀ (k := k)).Linear k := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only [meshShiftOrbitProjectionFunctor]
  infer_instance

/-- Reindexing additive deck degrees by the corresponding projection fibre
identifies an orbit Hom direct sum with the fixed-source covering direct
sum. -/
noncomputable def shiftOrbitTargetFiberLinearEquiv
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀)) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    MagnitudeConjecture.CoveringHom.ShiftOrbitHom
        (Additive (FundamentalGroup T x₀)) X Y ≃ₗ[k]
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (meshProjectionFunctor T x₀ (k := k))
          ((meshProjectionFunctor T x₀ (k := k)).obj Y))
        (fun Z ↦ X ⟶ Z.1) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let e := deckShiftTargetFiberEquiv T x₀ (k := k) Y
  let M : MagnitudeConjecture.LinearCovering.Fiber
      (meshProjectionFunctor T x₀ (k := k))
      ((meshProjectionFunctor T x₀ (k := k)).obj Y) → Type _ :=
    fun Z ↦ X ⟶ Z.1
  change
    DirectSum (Additive (FundamentalGroup T x₀))
        (fun a ↦ X ⟶
          (deckMeshEndofunctor T x₀ a.toMul⁻¹ (k := k)).obj Y) ≃ₗ[k]
      DirectSum _ M
  let reindex :
      DirectSum (Additive (FundamentalGroup T x₀)) (fun a ↦ M (e a)) ≃ₗ[k]
        DirectSum _ (fun Z ↦ M (e (e.symm Z))) :=
    DirectSum.lequivCongrLeft k e
  let castFibers : DirectSum _ (fun Z ↦ M (e (e.symm Z))) ≃ₗ[k]
      DirectSum _ M :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun Z ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply Z)
  exact reindex.trans castFibers

@[simp]
theorem shiftOrbitTargetFiberLinearEquiv_shiftOrbitLof
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀))
    (a : Additive (FundamentalGroup T x₀))
    (f : let D := deckMeshCoherentDeckShift T x₀ (k := k)
      letI := D.hasShift
      MagnitudeConjecture.CoveringHom.ShiftHom X Y a) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    shiftOrbitTargetFiberLinearEquiv T x₀ (k := k) X Y
        (MagnitudeConjecture.CoveringHom.shiftOrbitLof
          (k := k) X Y a f) =
      MagnitudeConjecture.LinearCovering.targetFiberLof
        (k := k) (meshProjectionFunctor T x₀ (k := k)) X
        ((meshProjectionFunctor T x₀ (k := k)).obj Y)
        (deckShiftTargetFiberEquiv T x₀ (k := k) Y a) f := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  classical
  let e := deckShiftTargetFiberEquiv T x₀ (k := k) Y
  let M : MagnitudeConjecture.LinearCovering.Fiber
      (meshProjectionFunctor T x₀ (k := k))
      ((meshProjectionFunctor T x₀ (k := k)).obj Y) → Type _ :=
    fun Z ↦ X ⟶ Z.1
  change shiftOrbitTargetFiberLinearEquiv T x₀ (k := k) X Y
      (DirectSum.of (fun a ↦ M (e a)) a f) =
    DirectSum.of M (e a) f
  unfold shiftOrbitTargetFiberLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e a f

/-- On one homogeneous deck degree, the descended orbit projection is the
corresponding summand of the fixed-source covering map. -/
theorem meshShiftOrbitProjectionFunctor_map_shiftOrbitLof
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀))
    (a : Additive (FundamentalGroup T x₀))
    (f : let D := deckMeshCoherentDeckShift T x₀ (k := k)
      letI := D.hasShift
      MagnitudeConjecture.CoveringHom.ShiftHom X Y a) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (meshShiftOrbitProjectionFunctor T x₀ (k := k)).map
        (MagnitudeConjecture.CoveringHom.shiftOrbitLof
          (k := k) X Y a f) =
      MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (meshProjectionFunctor T x₀ (k := k)) X
        ((meshProjectionFunctor T x₀ (k := k)).obj Y)
        (MagnitudeConjecture.LinearCovering.targetFiberLof
          (k := k) (meshProjectionFunctor T x₀ (k := k)) X
          ((meshProjectionFunctor T x₀ (k := k)).obj Y)
          (deckShiftTargetFiberEquiv T x₀ (k := k) Y a) f) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : HasShift (RawCategory (k := k) T)
      (Additive (FundamentalGroup T x₀)) :=
    MagnitudeConjecture.CoveringHom.trivialHasShift _ _
  letI := meshProjectionCommShift T x₀ (k := k)
  dsimp only
  rw [MagnitudeConjecture.CoveringHom.shiftOrbitLof_apply]
  change
    (MagnitudeConjecture.CoveringHom.shiftOrbitDescendedFunctor
      (k := k) (A := Additive (FundamentalGroup T x₀))
      (meshProjectionFunctor T x₀ (k := k))).map
        (MagnitudeConjecture.CoveringHom.shiftOrbitOf X Y a f) = _
  rw [MagnitudeConjecture.CoveringHom.shiftOrbitDescendedFunctor_map_of,
    MagnitudeConjecture.LinearCovering.targetFiberHomMap_lof]
  unfold MagnitudeConjecture.CoveringHom.shiftOrbitDescendHomogeneousMap
  rw [meshProjectionCommShift_hom_app]
  rfl

/-- The covering Hom isomorphism, reindexed by deck degrees, is the Hom map
of the descended orbit projection. -/
noncomputable def meshShiftOrbitProjectionHomLinearEquiv
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀)) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    MagnitudeConjecture.CoveringHom.ShiftOrbitHom
        (Additive (FundamentalGroup T x₀)) X Y ≃ₗ[k]
      ((meshProjectionFunctor T x₀ (k := k)).obj X ⟶
        (meshProjectionFunctor T x₀ (k := k)).obj Y) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (shiftOrbitTargetFiberLinearEquiv T x₀ (k := k) X Y).trans
    ((meshProjectionFunctor_isCovering T x₀ (k := k)).targetFiberHomLinearEquiv
      X ((meshProjectionFunctor T x₀ (k := k)).obj Y))

@[simp]
theorem meshShiftOrbitProjectionHomLinearEquiv_apply
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀))
    (f : let D := deckMeshCoherentDeckShift T x₀ (k := k)
      letI := D.hasShift
      letI := D.additiveShift
      MagnitudeConjecture.CoveringHom.ShiftOrbitHom
        (Additive (FundamentalGroup T x₀)) X Y) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    meshShiftOrbitProjectionHomLinearEquiv T x₀ (k := k) X Y f =
      (meshShiftOrbitProjectionFunctor T x₀ (k := k)).map f := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  classical
  dsimp only at f ⊢
  refine DirectSum.induction_on f ?_ ?_ ?_
  · rw [map_zero,
      (meshShiftOrbitProjectionFunctor T x₀ (k := k)).map_zero]
    rfl
  · intro a fa
    change
      meshShiftOrbitProjectionHomLinearEquiv T x₀ (k := k) X Y
          (MagnitudeConjecture.CoveringHom.shiftOrbitLof
            (k := k) X Y a fa) =
        (meshShiftOrbitProjectionFunctor T x₀ (k := k)).map
          (MagnitudeConjecture.CoveringHom.shiftOrbitLof
            (k := k) X Y a fa)
    unfold meshShiftOrbitProjectionHomLinearEquiv
    dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [shiftOrbitTargetFiberLinearEquiv_shiftOrbitLof,
      MagnitudeConjecture.LinearCovering.IsCovering.targetFiberHomLinearEquiv_apply,
      meshShiftOrbitProjectionFunctor_map_shiftOrbitLof]
  · intro f₁ f₂ hf₁ hf₂
    rw [map_add,
      (meshShiftOrbitProjectionFunctor T x₀ (k := k)).map_add]
    exact congrArg₂ (.+.) hf₁ hf₂

/-- The descended orbit projection is bijective on every Hom space. -/
theorem meshShiftOrbitProjectionFunctor_map_bijective
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (X Y : RawCategory (k := k) (rightMeshData T x₀)) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Bijective
      ((meshShiftOrbitProjectionFunctor T x₀ (k := k)).map :
        MagnitudeConjecture.CoveringHom.ShiftOrbitHom
            (Additive (FundamentalGroup T x₀)) X Y →
          ((meshProjectionFunctor T x₀ (k := k)).obj X ⟶
            (meshProjectionFunctor T x₀ (k := k)).obj Y)) := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let e := meshShiftOrbitProjectionHomLinearEquiv T x₀ (k := k) X Y
  constructor
  · intro f g hfg
    apply e.injective
    rw [meshShiftOrbitProjectionHomLinearEquiv_apply,
      meshShiftOrbitProjectionHomLinearEquiv_apply, hfg]
  · intro f
    refine ⟨e.symm f, ?_⟩
    rw [← meshShiftOrbitProjectionHomLinearEquiv_apply,
      e.apply_symm_apply]

/-- The descended orbit projection is fully faithful. -/
noncomputable def meshShiftOrbitProjectionFunctorFullyFaithful
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)] :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (meshShiftOrbitProjectionFunctor T x₀ (k := k)).FullyFaithful := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := meshShiftOrbitProjectionFunctor T x₀ (k := k)
  letI : F.Faithful :=
    ⟨fun h ↦
      (meshShiftOrbitProjectionFunctor_map_bijective
        T x₀ (k := k) _ _).injective h⟩
  letI : F.Full :=
    ⟨(meshShiftOrbitProjectionFunctor_map_bijective
      T x₀ (k := k) _ _).surjective⟩
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- Based connectedness makes the descended orbit projection surjective on
objects. -/
theorem meshShiftOrbitProjectionFunctor_obj_surjective
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (hconnected : IsWalkConnectedAt T x₀) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Surjective
      (meshShiftOrbitProjectionFunctor T x₀ (k := k)).obj := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  rintro ⟨Y⟩
  obtain ⟨W, hW⟩ := vertex_surjective T x₀ hconnected
    (MagnitudeConjecture.LinearPathCategory.vertex Y)
  refine ⟨obj (k := k) (rightMeshData T x₀) W, ?_⟩
  change
    (meshProjectionFunctor T x₀ (k := k)).obj
        (obj (k := k) (rightMeshData T x₀) W) = ⟨Y⟩
  unfold meshProjectionFunctor
  rw [(cover T x₀).functorUsingSourceFintype_obj_obj]
  apply CategoryTheory.Quotient.ext
  change W.1 = MagnitudeConjecture.LinearPathCategory.vertex Y
  exact hW

/-- For a connected translation quiver, its raw mesh category is the deck
shift-orbit category of the universal raw mesh category. -/
theorem meshShiftOrbitProjectionFunctor_isEquivalence
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (hconnected : IsWalkConnectedAt T x₀) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (meshShiftOrbitProjectionFunctor T x₀ (k := k)).IsEquivalence := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := meshShiftOrbitProjectionFunctor T x₀ (k := k)
  let hff := meshShiftOrbitProjectionFunctorFullyFaithful T x₀ (k := k)
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := F.essSurj_of_surj
        (meshShiftOrbitProjectionFunctor_obj_surjective
          T x₀ (k := k) hconnected) }

/-- The explicit equivalence from the universal deck orbit to the downstairs
raw mesh category. -/
noncomputable def meshShiftOrbitEquivalence
    (T : RightMeshData Q) (x₀ : Q)
    {k : Type u} [Field k] [∀ y : Q, Fintype (Quiver.Star y)]
    (hconnected : IsWalkConnectedAt T x₀) :
    let D := deckMeshCoherentDeckShift T x₀ (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    MagnitudeConjecture.CoveringHom.ShiftOrbitCategory
        (RawCategory (k := k) (rightMeshData T x₀))
        (Additive (FundamentalGroup T x₀)) ≌
      RawCategory (k := k) T := by
  let D := deckMeshCoherentDeckShift T x₀ (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := meshShiftOrbitProjectionFunctor T x₀ (k := k)
  letI : F.IsEquivalence :=
    meshShiftOrbitProjectionFunctor_isEquivalence
      T x₀ (k := k) hconnected
  exact F.asEquivalence

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
