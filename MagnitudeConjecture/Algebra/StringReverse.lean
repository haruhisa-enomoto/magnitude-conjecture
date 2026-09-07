import MagnitudeConjecture.Algebra.StringModuleExtension

/-!
# Reversal of string representations

A prefix occurrence in a word becomes the reversed complementary suffix in
the reversed word.  This file begins the explicit reversal equivalence needed
to transport right-endpoint hook and cohook constructions to the left
endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

namespace PositionAt

/-- The complementary suffix belonging to a prefix position. -/
def suffix {C : Word R} {x : Q} (i : C.PositionAt x) :
    SignedPath x C.target :=
  Classical.choose i.2

/-- A position prefix followed by its chosen suffix recovers the word. -/
theorem prefix_comp_suffix {C : Word R} {x : Q}
    (i : C.PositionAt x) :
    C.path = i.1.comp i.suffix :=
  Classical.choose_spec i.2

/-- The suffix length is the complementary word index. -/
theorem suffix_length {C : Word R} {x : Q} (i : C.PositionAt x) :
    i.suffix.length = C.length - i.index := by
  have hlength := congrArg Quiver.Path.length i.prefix_comp_suffix
  rw [Quiver.Path.length_comp] at hlength
  change i.suffix.length = C.path.length - i.1.length
  omega

end PositionAt

/-- Reverse a prefix position by taking the reverse of its complementary
suffix. -/
def reversePosition (C : Word R) {x : Q} (i : C.PositionAt x) :
    C.reverse.PositionAt x := by
  refine ⟨i.suffix.reverse, ?_⟩
  refine ⟨i.1.reverse, ?_⟩
  have h := congrArg Quiver.Path.reverse i.prefix_comp_suffix
  change C.path.reverse = i.suffix.reverse.comp i.1.reverse
  simpa only [Quiver.Path.reverse_comp] using h

@[simp]
theorem reversePosition_val (C : Word R) {x : Q}
    (i : C.PositionAt x) :
    (reversePosition C i).1 = i.suffix.reverse := rfl

@[simp]
theorem reversePosition_index (C : Word R) {x : Q}
    (i : C.PositionAt x) :
    (reversePosition C i).index = C.length - i.index := by
  change (reversePosition C i).1.length = C.length - i.index
  rw [reversePosition_val]
  have hlength : i.suffix.reverse.length = i.suffix.length :=
    @length_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ i.suffix
  exact hlength.trans i.suffix_length

/-- Undo reversal of a prefix position without casting through the bundled
identity `C.reverse.reverse = C`. -/
def unreversePosition (C : Word R) {x : Q}
    (j : C.reverse.PositionAt x) : C.PositionAt x := by
  refine ⟨j.suffix.reverse, ?_⟩
  refine ⟨j.1.reverse, ?_⟩
  have hfactor := j.prefix_comp_suffix
  change C.path.reverse = j.1.comp j.suffix at hfactor
  have h := congrArg Quiver.Path.reverse hfactor
  have hcomp : (j.1.comp j.suffix).reverse =
      j.suffix.reverse.comp j.1.reverse :=
    @Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ _ j.1 j.suffix
  have h' : C.path.reverse.reverse =
      j.suffix.reverse.comp j.1.reverse := h.trans hcomp
  exact (@Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
    (Quiver.symmetrifyQuiver Q) _ _ _ C.path).symm.trans h'

@[simp]
theorem unreversePosition_val (C : Word R) {x : Q}
    (j : C.reverse.PositionAt x) :
    (unreversePosition C j).1 = j.suffix.reverse := rfl

@[simp]
theorem unreversePosition_index (C : Word R) {x : Q}
    (j : C.reverse.PositionAt x) :
    (unreversePosition C j).index = C.length - j.index := by
  change (unreversePosition C j).1.length = C.length - j.index
  rw [unreversePosition_val]
  have hlength : j.suffix.reverse.length = j.suffix.length :=
    @length_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ j.suffix
  exact hlength.trans (j.suffix_length.trans
    (congrArg (fun n ↦ n - j.index) (reverse_length R C)))

/-- Prefix occurrences at every displayed vertex are canonically equivalent
under word reversal. -/
def reversePositionEquiv (C : Word R) (x : Q) :
    C.PositionAt x ≃ C.reverse.PositionAt x where
  toFun := reversePosition C
  invFun := unreversePosition C
  left_inv i := by
    apply PositionAt.ext_index
    have hi := i.index_le
    rw [unreversePosition_index, reversePosition_index]
    omega
  right_inv j := by
    apply PositionAt.ext_index
    have hj := j.index_le
    rw [reverse_length] at hj
    rw [reversePosition_index, unreversePosition_index]
    omega

/-- Reversal preserves the displayed-arrow adjacency relation on prefix
occurrences. -/
theorem arrowStep_reversePosition (C : Word R) {x y : Q}
    (a : x ⟶ y) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    C.reverse.ArrowStep a (reversePosition C i) (reversePosition C j) := by
  rcases hij with hpositive | hnegative
  · right
    have hsuffix :
        i.suffix = (positiveArrow a).toPath.comp j.suffix := by
      apply Quiver.Path.comp_injective_right i.1
      calc
        i.1.comp i.suffix = C.path := i.prefix_comp_suffix.symm
        _ = j.1.comp j.suffix := j.prefix_comp_suffix
        _ = (i.1.comp (positiveArrow a).toPath).comp j.suffix := by
          rw [hpositive]
        _ = i.1.comp ((positiveArrow a).toPath.comp j.suffix) :=
          Quiver.Path.comp_assoc _ _ _
    have hreverse := congrArg Quiver.Path.reverse hsuffix
    change i.suffix.reverse =
      j.suffix.reverse.comp (negativeArrow a).toPath
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_positiveArrow] using hreverse
  · left
    have hsuffix :
        j.suffix = (negativeArrow a).toPath.comp i.suffix := by
      apply Quiver.Path.comp_injective_right j.1
      calc
        j.1.comp j.suffix = C.path := j.prefix_comp_suffix.symm
        _ = i.1.comp i.suffix := i.prefix_comp_suffix
        _ = (j.1.comp (negativeArrow a).toPath).comp i.suffix := by
          rw [hnegative]
        _ = j.1.comp ((negativeArrow a).toPath.comp i.suffix) :=
          Quiver.Path.comp_assoc _ _ _
    have hreverse := congrArg Quiver.Path.reverse hsuffix
    change j.suffix.reverse =
      i.suffix.reverse.comp (positiveArrow a).toPath
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow] using hreverse

/-- The inverse position map also preserves displayed-arrow adjacency. -/
theorem arrowStep_unreversePosition (C : Word R) {x y : Q}
    (a : x ⟶ y) (i : C.reverse.PositionAt x)
    (j : C.reverse.PositionAt y)
    (hij : C.reverse.ArrowStep a i j) :
    C.ArrowStep a (unreversePosition C i) (unreversePosition C j) := by
  rcases hij with hpositive | hnegative
  · right
    have hsuffix :
        i.suffix = (positiveArrow a).toPath.comp j.suffix := by
      apply Quiver.Path.comp_injective_right i.1
      calc
        i.1.comp i.suffix = C.reverse.path := i.prefix_comp_suffix.symm
        _ = j.1.comp j.suffix := j.prefix_comp_suffix
        _ = (i.1.comp (positiveArrow a).toPath).comp j.suffix := by
          rw [hpositive]
        _ = i.1.comp ((positiveArrow a).toPath.comp j.suffix) :=
          Quiver.Path.comp_assoc _ _ _
    have hreverse := congrArg Quiver.Path.reverse hsuffix
    change i.suffix.reverse =
      j.suffix.reverse.comp (negativeArrow a).toPath
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_positiveArrow] using hreverse
  · left
    have hsuffix :
        j.suffix = (negativeArrow a).toPath.comp i.suffix := by
      apply Quiver.Path.comp_injective_right j.1
      calc
        j.1.comp j.suffix = C.reverse.path := j.prefix_comp_suffix.symm
        _ = i.1.comp i.suffix := i.prefix_comp_suffix
        _ = (j.1.comp (negativeArrow a).toPath).comp i.suffix := by
          rw [hnegative]
        _ = j.1.comp ((negativeArrow a).toPath.comp i.suffix) :=
          Quiver.Path.comp_assoc _ _ _
    have hreverse := congrArg Quiver.Path.reverse hsuffix
    change j.suffix.reverse =
      i.suffix.reverse.comp (positiveArrow a).toPath
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow] using hreverse

/-- Reindex the position basis of a string word by reversed occurrences. -/
def reverseSpaceEquiv (C : Word R) (x : Q) :
    C.Space x ≃ₗ[k] C.reverse.Space x :=
  Finsupp.domLCongr (reversePositionEquiv C x)

@[simp]
theorem reverseSpaceEquiv_single (C : Word R) {x : Q}
    (i : C.PositionAt x) (c : k) :
    reverseSpaceEquiv C x (Finsupp.single i c) =
      Finsupp.single (reversePosition C i) c :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem reverseSpaceEquiv_symm_single (C : Word R) {x : Q}
    (j : C.reverse.PositionAt x) (c : k) :
    (reverseSpaceEquiv C x).symm (Finsupp.single j c) =
      Finsupp.single (unreversePosition C j) c := by
  have hj : reversePosition C (unreversePosition C j) = j :=
    (reversePositionEquiv C x).right_inv j
  have hu : unreversePosition C (reversePosition C (unreversePosition C j)) =
      unreversePosition C j :=
    (reversePositionEquiv C x).left_inv (unreversePosition C j)
  rw [← hj, ← reverseSpaceEquiv_single]
  rw [hu]
  exact (reverseSpaceEquiv C x).symm_apply_apply _

/-- Reversal reindexing commutes with every displayed-arrow action on a
basis vector. -/
theorem reverseSpaceEquiv_arrowLinearMap_single
    (C : Word R) {x y : Q} (a : x ⟶ y) (i : C.PositionAt x) :
    reverseSpaceEquiv C y
        (C.arrowLinearMap a (Finsupp.single i 1)) =
      C.reverse.arrowLinearMap a
        (reverseSpaceEquiv C x (Finsupp.single i 1)) := by
  classical
  by_cases hex : ∃ j : C.PositionAt y, C.ArrowStep a i j
  · let j := Classical.choose hex
    have hij : C.ArrowStep a i j := Classical.choose_spec hex
    rw [C.arrowLinearMap_single_one_of_step a i j hij,
      reverseSpaceEquiv_single, reverseSpaceEquiv_single]
    symm
    apply C.reverse.arrowLinearMap_single_one_of_step
    exact arrowStep_reversePosition C a i j hij
  · rw [C.arrowLinearMap_single, one_smul,
      C.arrowOnBasis_eq_zero_of_not_exists a i hex, map_zero,
      reverseSpaceEquiv_single, C.reverse.arrowLinearMap_single, one_smul]
    symm
    apply C.reverse.arrowOnBasis_eq_zero_of_not_exists
    rintro ⟨l, hil⟩
    apply hex
    refine ⟨unreversePosition C l, ?_⟩
    have hstep := arrowStep_unreversePosition C a
      (reversePosition C i) l hil
    have hi : unreversePosition C (reversePosition C i) = i :=
      (reversePositionEquiv C x).left_inv i
    rw [hi] at hstep
    exact hstep

/-- Reversal reindexing is a morphism of quiver representations. -/
theorem reverseSpaceEquiv_arrowLinearMap
    (C : Word R) {x y : Q} (a : x ⟶ y) (v : C.Space x) :
    reverseSpaceEquiv C y (C.arrowLinearMap a v) =
      C.reverse.arrowLinearMap a (reverseSpaceEquiv C x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul,
        reverseSpaceEquiv_arrowLinearMap_single]

/-- A string word and its reverse carry canonically isomorphic quiver
representations. -/
def reverseQuiverRepresentationIso (C : Word R) :
    C.quiverRepresentation ≅ C.reverse.quiverRepresentation :=
  Paths.liftNatIso
    (fun x ↦ (reverseSpaceEquiv C x).toModuleIso)
    (fun {x y} a ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change reverseSpaceEquiv C y (C.arrowLinearMap a v) =
        C.reverse.arrowLinearMap a (reverseSpaceEquiv C x v)
      exact reverseSpaceEquiv_arrowLinearMap C a v)

/-- In the opposite-module realization, reversal gives an isomorphism in the
opposite direction. -/
def reverseFreeRightModuleAuxIso (C : Word R) :
    C.reverse.freeRightModuleAux ≅ C.freeRightModuleAux :=
  LinearPathCategory.liftNatIso
    (fun x ↦ Opposite.op (ModuleCat.of k (C.reverse.Space x)))
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun a ↦ (ModuleCat.ofHom (C.reverse.arrowLinearMap a)).op)
    (fun a ↦ (ModuleCat.ofHom (C.arrowLinearMap a)).op)
    (fun x ↦ (reverseSpaceEquiv C x).toModuleIso.op)
    (fun {x y} a ↦ by
      change (ModuleCat.ofHom (C.reverse.arrowLinearMap a)).op ≫
          (ModuleCat.ofHom (reverseSpaceEquiv C x).toLinearMap).op =
        (ModuleCat.ofHom (reverseSpaceEquiv C y).toLinearMap).op ≫
          (ModuleCat.ofHom (C.arrowLinearMap a)).op
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change C.reverse.arrowLinearMap a (reverseSpaceEquiv C x v) =
        reverseSpaceEquiv C y (C.arrowLinearMap a v)
      exact (reverseSpaceEquiv_arrowLinearMap C a v).symm)

/-- The reversal isomorphism descends through a monomial relation quotient. -/
def reverseQuotientRightModuleAuxIso (C : Word R)
    (hmono : IsMonomial R) :
    C.reverse.quotientRightModuleAux hmono ≅
      C.quotientRightModuleAux hmono :=
  HomIdeal.quotientLiftNatIso
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := C.reverse.freeRightModuleAux)
    (C.reverse.relationIdeal_isKilledBy hmono)
    (C.relationIdeal_isKilledBy hmono)
    C.reverseFreeRightModuleAuxIso

/-- A string word and its reverse define canonically isomorphic right
modules. -/
def reverseRightModuleIso (C : Word R) (hmono : IsMonomial R) :
    C.rightModule hmono ≅ C.reverse.rightModule hmono :=
  NatIso.ofComponents
    (fun X ↦ (reverseQuotientRightModuleAuxIso C hmono).app X.unop |>.unop)
    (fun f ↦ by
      apply Quiver.Hom.op_inj
      exact ((reverseQuotientRightModuleAuxIso C hmono).hom.naturality
        f.unop).symm)

@[simp]
theorem reverseRightModuleIso_hom_app_obj
    (C : Word R) (hmono : IsMonomial R) (x : Q) :
    (reverseRightModuleIso C hmono).hom.app (Opposite.op (obj R x)) =
      ModuleCat.ofHom (reverseSpaceEquiv C x).toLinearMap :=
  rfl

@[simp]
theorem reverseRightModuleIso_inv_app_obj
    (C : Word R) (hmono : IsMonomial R) (x : Q) :
    (reverseRightModuleIso C hmono).inv.app (Opposite.op (obj R x)) =
      ModuleCat.ofHom (reverseSpaceEquiv C x).symm.toLinearMap :=
  rfl

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
