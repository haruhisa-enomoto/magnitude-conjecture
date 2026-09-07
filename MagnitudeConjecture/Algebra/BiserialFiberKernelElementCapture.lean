import MagnitudeConjecture.Algebra.BiserialQuotientBranch
import MagnitudeConjecture.Algebra.JacobsonRadicalAction

/-!
# Element capture in a biserial fiber kernel

The element calculation in the first Pogorzały--Skowroński obstruction
produces a vector with two nonzero socle coordinates inside a hypothetical
uniserial summand, while that summand already contains one coordinate socle.
The lemmas below prove that these data force the summand to contain the whole
fiber-kernel socle.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Embed the left branch socle as the left coordinate of the fiber
kernel. -/
def fiberKernelLeftSocleMap
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker) :
    moduleSocle Aᵐᵒᵖ Y →ₗ[Aᵐᵒᵖ] fiberKernelFGObj Y Z Top f g :=
  let i : moduleSocle Aᵐᵒᵖ Y →ₗ[Aᵐᵒᵖ]
      (fiberKernelMap Y Z Top f g).ker := {
    toFun y := ⟨(y.1, 0), by
      change fiberKernelMap Y Z Top f g (y.1, 0) = 0
      simp [fiberKernelMap, LinearMap.mem_ker.mp (hYkill y.2)]⟩
    map_add' _ _ := by
      apply Subtype.ext
      apply Prod.ext <;> simp
    map_smul' _ _ := by
      apply Subtype.ext
      apply Prod.ext <;> simp }
  (fiberKernelFGObjLinearEquiv Y Z Top f g).symm.toLinearMap.comp i

/-- Embed the right branch socle as the right coordinate of the fiber
kernel. -/
def fiberKernelRightSocleMap
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    moduleSocle Aᵐᵒᵖ Z →ₗ[Aᵐᵒᵖ] fiberKernelFGObj Y Z Top f g :=
  let i : moduleSocle Aᵐᵒᵖ Z →ₗ[Aᵐᵒᵖ]
      (fiberKernelMap Y Z Top f g).ker := {
    toFun z := ⟨(0, z.1), by
      change fiberKernelMap Y Z Top f g (0, z.1) = 0
      simp [fiberKernelMap, LinearMap.mem_ker.mp (hZkill z.2)]⟩
    map_add' _ _ := by
      apply Subtype.ext
      apply Prod.ext <;> simp
    map_smul' _ _ := by
      apply Subtype.ext
      apply Prod.ext <;> simp }
  (fiberKernelFGObjLinearEquiv Y Z Top f g).symm.toLinearMap.comp i

/-- The ambient inclusion sends the left socle embedding to `(y,0)`. -/
@[simp]
theorem fiberKernelInclusion_leftSocleMap
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (y : moduleSocle Aᵐᵒᵖ Y) :
    fiberKernelInclusion Y Z Top f g (fiberKernelLeftSocleMap Y Z Top f g hYkill y) =
      (y.1, 0) := by
  rfl

/-- The ambient inclusion sends the right socle embedding to `(0,z)`. -/
@[simp]
theorem fiberKernelInclusion_rightSocleMap
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (z : moduleSocle Aᵐᵒᵖ Z) :
    fiberKernelInclusion Y Z Top f g (fiberKernelRightSocleMap Y Z Top f g hZkill z) =
      (0, z.1) := by
  rfl

/-- The left socle embedding is injective. -/
theorem fiberKernelLeftSocleMap_injective
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker) :
    Function.Injective (fiberKernelLeftSocleMap Y Z Top f g hYkill) := by
  intro y y' h
  apply Subtype.ext
  have hi := congrArg
    (fun w : Y × Z ↦ w.1)
    (congrArg (fiberKernelInclusion Y Z Top f g) h)
  simpa using hi

/-- The right socle embedding is injective. -/
theorem fiberKernelRightSocleMap_injective
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    Function.Injective (fiberKernelRightSocleMap Y Z Top f g hZkill) := by
  intro z z' h
  apply Subtype.ext
  have hi := congrArg
    (fun w : Y × Z ↦ w.2)
    (congrArg (fiberKernelInclusion Y Z Top f g) h)
  simpa using hi

/-- The left coordinate copy of the branch socle in the fiber kernel. -/
def fiberKernelLeftSocleSubmodule
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker) :
    Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) :=
  (fiberKernelLeftSocleMap Y Z Top f g hYkill).range

/-- The right coordinate copy of the branch socle in the fiber kernel. -/
def fiberKernelRightSocleSubmodule
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) :=
  (fiberKernelRightSocleMap Y Z Top f g hZkill).range

/-- A submodule of a fiber kernel contains a vector with two nonzero branch
socle coordinates. -/
def HasMixedSocleCoordinates
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)) : Prop :=
  ∃ y : moduleSocle Aᵐᵒᵖ Y, ∃ z : moduleSocle Aᵐᵒᵖ Z,
    y ≠ 0 ∧ z ≠ 0 ∧
      ∃ w : fiberKernelFGObj Y Z Top f g, w ∈ P ∧
        fiberKernelInclusion Y Z Top f g w = (y.1, z.1)

/-- A source-shaped witness for mixed socle coordinates: one scalar sends the
two coordinates of a vector in `P` to nonzero elements of the corresponding
branch socles. -/
def HasMixedSocleSmulWitness
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)) : Prop :=
  ∃ u : fiberKernelFGObj Y Z Top f g, ∃ r : Aᵐᵒᵖ,
    u ∈ P ∧
      r • (fiberKernelInclusion Y Z Top f g u).1 ≠ 0 ∧
      r • (fiberKernelInclusion Y Z Top f g u).2 ≠ 0 ∧
      r • (fiberKernelInclusion Y Z Top f g u).1 ∈ moduleSocle Aᵐᵒᵖ Y ∧
      r • (fiberKernelInclusion Y Z Top f g u).2 ∈ moduleSocle Aᵐᵒᵖ Z

/-- A scalar-action witness produces a vector with mixed nonzero socle
coordinates. -/
theorem hasMixedSocleCoordinates_of_smulWitness
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (h : HasMixedSocleSmulWitness Y Z Top f g P) :
    HasMixedSocleCoordinates Y Z Top f g P := by
  obtain ⟨u, r, hu, hy, hz, hySocle, hzSocle⟩ := h
  let y : moduleSocle Aᵐᵒᵖ Y :=
    ⟨r • (fiberKernelInclusion Y Z Top f g u).1, hySocle⟩
  let z : moduleSocle Aᵐᵒᵖ Z :=
    ⟨r • (fiberKernelInclusion Y Z Top f g u).2, hzSocle⟩
  refine ⟨y, z, ?_, ?_, r • u, P.smul_mem r hu, ?_⟩
  · intro hzero
    exact hy (congrArg Subtype.val hzero)
  · intro hzero
    exact hz (congrArg Subtype.val hzero)
  · change fiberKernelInclusion Y Z Top f g (r • u) =
      (r • (fiberKernelInclusion Y Z Top f g u).1,
        r • (fiberKernelInclusion Y Z Top f g u).2)
    rw [(fiberKernelInclusion Y Z Top f g).map_smul]
    rfl

include k in
/-- The radical-square calculation for a length-three uniserial submodule
produces a source-shaped mixed-socle witness as soon as nonvanishing of the
two ambient coordinates is known.  Membership of those coordinates in the
branch socles is automatic: the submodule socle maps into the fiber-kernel
socle, and the latter maps onto the product of the branch socles. -/
theorem hasMixedSocleSmulWitness_of_length_three
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    [IsArtinian Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)]
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (hPne : P ≠ ⊥) (hPuniserial : IsUniserialModule Aᵐᵒᵖ P)
    (hPlength : Module.length Aᵐᵒᵖ P = 3)
    (u : P) (hu : u ∉ Module.jacobson Aᵐᵒᵖ P)
    (hnonzero : ∀ r ∈ Ring.jacobson Aᵐᵒᵖ ^ 2,
      r • u ≠ 0 →
        r • (fiberKernelInclusion Y Z Top f g u.1).1 ≠ 0 ∧
          r • (fiberKernelInclusion Y Z Top f g u.1).2 ≠ 0) :
    HasMixedSocleSmulWitness Y Z Top f g P := by
  letI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hPne
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨r, hr, hru, hruSocle⟩ :=
    exists_radicalSquare_smul_ne_zero_mem_socle
      hPuniserial hPlength u hu
  have hcoordsNonzero := hnonzero r hr hru
  have hruSocleW : P.subtype (r • u) ∈
      moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) := by
    exact map_moduleSocle_le_of_injective P.subtype P.subtype_injective
      ⟨r • u, hruSocle, rfl⟩
  have hcoordsSocle : fiberKernelInclusion Y Z Top f g
      (P.subtype (r • u)) ∈
        (moduleSocle Aᵐᵒᵖ Y).prod (moduleSocle Aᵐᵒᵖ Z) := by
    have hmapped : fiberKernelInclusion Y Z Top f g
        (P.subtype (r • u)) ∈
          (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)).map
            (fiberKernelInclusion Y Z Top f g) :=
      ⟨P.subtype (r • u), hruSocleW, rfl⟩
    rw [map_moduleSocle_fiberKernel_eq_prod
      Y Z Top f g hYsimple hZsimple hYkill hZkill] at hmapped
    exact hmapped
  refine ⟨u.1, r, u.2, hcoordsNonzero.1, hcoordsNonzero.2, ?_, ?_⟩
  · simpa using hcoordsSocle.1
  · simpa using hcoordsSocle.2

/-- A submodule containing both coordinate socles contains the entire socle
of the fiber kernel. -/
theorem moduleSocle_fiberKernel_le_of_coordinateSocles_le
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (hleft : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ≤ P)
    (hright : fiberKernelRightSocleSubmodule Y Z Top f g hZkill ≤ P) :
    moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) ≤ P := by
  intro w hw
  let j := fiberKernelInclusion Y Z Top f g
  have hjw : j w ∈
      (moduleSocle Aᵐᵒᵖ Y).prod (moduleSocle Aᵐᵒᵖ Z) := by
    have hmapped : j w ∈
        (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)).map j :=
      ⟨w, hw, rfl⟩
    rw [map_moduleSocle_fiberKernel_eq_prod
      Y Z Top f g hYsimple hZsimple hYkill hZkill] at hmapped
    exact hmapped
  let y : moduleSocle Aᵐᵒᵖ Y := ⟨(j w).1, hjw.1⟩
  let z : moduleSocle Aᵐᵒᵖ Z := ⟨(j w).2, hjw.2⟩
  have hly : fiberKernelLeftSocleMap Y Z Top f g hYkill y ∈ P :=
    hleft ⟨y, rfl⟩
  have hrz : fiberKernelRightSocleMap Y Z Top f g hZkill z ∈ P :=
    hright ⟨z, rfl⟩
  have heq : fiberKernelLeftSocleMap Y Z Top f g hYkill y +
      fiberKernelRightSocleMap Y Z Top f g hZkill z = w := by
    apply fiberKernelInclusion_injective Y Z Top f g
    simp [j, y, z]
  rw [← heq]
  exact P.add_mem hly hrz

/-- If the two simple branch socles are non-isomorphic, every nonzero
submodule with simple intrinsic socle contains one of their coordinate
copies. -/
theorem fiberKernel_coordinateSocle_le_of_simpleSocle
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hnoniso : ¬ Nonempty
      (moduleSocle Aᵐᵒᵖ Y ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    [IsArtinian Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)]
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (hPsocleSimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ P)) :
    fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ≤ P ∨
      fiberKernelRightSocleSubmodule Y Z Top f g hZkill ≤ P := by
  let W := fiberKernelFGObj Y Z Top f g
  let eW : moduleSocle Aᵐᵒᵖ W ≃ₗ[Aᵐᵒᵖ]
      moduleSocle Aᵐᵒᵖ Y × moduleSocle Aᵐᵒᵖ Z :=
    fiberKernelSocleLinearEquiv Y Z Top f g
      hYsimple hZsimple hYkill hZkill
  letI : Nontrivial (moduleSocle Aᵐᵒᵖ P) := hPsocleSimple.nontrivial
  letI : Nontrivial P :=
    (moduleSocle Aᵐᵒᵖ P).subtype_injective.nontrivial
  have hmapSocle : (moduleSocle Aᵐᵒᵖ P).map P.subtype ≤
      moduleSocle Aᵐᵒᵖ W :=
    map_moduleSocle_le_of_injective P.subtype P.subtype_injective
  let i : moduleSocle Aᵐᵒᵖ P →ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ W :=
    (P.subtype.comp (moduleSocle Aᵐᵒᵖ P).subtype).codRestrict
      (moduleSocle Aᵐᵒᵖ W) (fun s ↦ hmapSocle ⟨s.1, s.2, rfl⟩)
  have hi : Function.Injective i := by
    intro x y hxy
    have hW : (x.1.1 : W) = y.1.1 :=
      congrArg (fun z : moduleSocle Aᵐᵒᵖ W ↦ (z.1 : W)) hxy
    have hP : x.1 = y.1 := P.subtype_injective hW
    exact (moduleSocle Aᵐᵒᵖ P).subtype_injective hP
  let q : moduleSocle Aᵐᵒᵖ P →ₗ[Aᵐᵒᵖ]
      (moduleSocle Aᵐᵒᵖ Y × moduleSocle Aᵐᵒᵖ Z) :=
    eW.toLinearMap.comp i
  have hq : Function.Injective q := eW.injective.comp hi
  let Q : Submodule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ Y × moduleSocle Aᵐᵒᵖ Z) :=
    LinearMap.range q
  have hQsimple : IsSimpleModule Aᵐᵒᵖ Q := by
    letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ P) := hPsocleSimple
    exact IsSimpleModule.congr (LinearEquiv.ofInjective q hq).symm
  have hleftSimple : IsSimpleModule Aᵐᵒᵖ
      (fiberKernelLeftSocleSubmodule Y Z Top f g hYkill) := by
    letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y) := hYsimple
    exact IsSimpleModule.congr
      (LinearEquiv.ofInjective
        (fiberKernelLeftSocleMap Y Z Top f g hYkill)
        (fiberKernelLeftSocleMap_injective Y Z Top f g hYkill)).symm
  have hrightSimple : IsSimpleModule Aᵐᵒᵖ
      (fiberKernelRightSocleSubmodule Y Z Top f g hZkill) := by
    letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z) := hZsimple
    exact IsSimpleModule.congr
      (LinearEquiv.ofInjective
        (fiberKernelRightSocleMap Y Z Top f g hZkill)
        (fiberKernelRightSocleMap_injective Y Z Top f g hZkill)).symm
  have hleftSocle : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ≤
      moduleSocle Aᵐᵒᵖ W :=
    le_moduleSocle_of_simple _ hleftSimple
  have hrightSocle : fiberKernelRightSocleSubmodule Y Z Top f g hZkill ≤
      moduleSocle Aᵐᵒᵖ W :=
    le_moduleSocle_of_simple _ hrightSimple
  rcases simpleSubmodule_prod_eq_coordinate hYsimple hZsimple hnoniso Q hQsimple with
    hQleft | hQright
  · left
    intro w hw
    obtain ⟨y, rfl⟩ := hw
    have hwSoc : fiberKernelLeftSocleMap Y Z Top f g hYkill y ∈
        moduleSocle Aᵐᵒᵖ W := hleftSocle ⟨y, rfl⟩
    let ws : moduleSocle Aᵐᵒᵖ W :=
      ⟨fiberKernelLeftSocleMap Y Z Top f g hYkill y, hwSoc⟩
    have hecoord : eW ws = (y, 0) := by
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    have hcoordMem : (y, 0) ∈ Q := by
      rw [hQleft]
      exact ⟨y, rfl⟩
    obtain ⟨s, hs⟩ := hcoordMem
    have hiEq : i s = ws := by
      apply eW.injective
      change q s = eW ws
      rw [hs, hecoord]
    have hval := congrArg Subtype.val hiEq
    change (s.1.1 : W) = fiberKernelLeftSocleMap Y Z Top f g hYkill y at hval
    rw [← hval]
    exact s.1.2
  · right
    intro w hw
    obtain ⟨z, rfl⟩ := hw
    have hwSoc : fiberKernelRightSocleMap Y Z Top f g hZkill z ∈
        moduleSocle Aᵐᵒᵖ W := hrightSocle ⟨z, rfl⟩
    let ws : moduleSocle Aᵐᵒᵖ W :=
      ⟨fiberKernelRightSocleMap Y Z Top f g hZkill z, hwSoc⟩
    have hecoord : eW ws = (0, z) := by
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    have hcoordMem : (0, z) ∈ Q := by
      rw [hQright]
      exact ⟨z, rfl⟩
    obtain ⟨s, hs⟩ := hcoordMem
    have hiEq : i s = ws := by
      apply eW.injective
      change q s = eW ws
      rw [hs, hecoord]
    have hval := congrArg Subtype.val hiEq
    change (s.1.1 : W) = fiberKernelRightSocleMap Y Z Top f g hZkill z at hval
    rw [← hval]
    exact s.1.2

/-- A submodule containing one coordinate socle and one vector whose two
socle coordinates are nonzero contains the whole fiber-kernel socle. -/
theorem moduleSocle_fiberKernel_le_of_mixed_of_coordinate_le
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (y : moduleSocle Aᵐᵒᵖ Y) (z : moduleSocle Aᵐᵒᵖ Z)
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hmixed : fiberKernelLeftSocleMap Y Z Top f g hYkill y +
      fiberKernelRightSocleMap Y Z Top f g hZkill z ∈ P)
    (hside : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ≤ P ∨
      fiberKernelRightSocleSubmodule Y Z Top f g hZkill ≤ P) :
    moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) ≤ P := by
  have hleftSimple : IsSimpleModule Aᵐᵒᵖ
      (fiberKernelLeftSocleSubmodule Y Z Top f g hYkill) := by
    letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y) :=
      hYsimple
    exact IsSimpleModule.congr
      (LinearEquiv.ofInjective
        (fiberKernelLeftSocleMap Y Z Top f g hYkill)
        (fiberKernelLeftSocleMap_injective Y Z Top f g hYkill)).symm
  have hrightSimple : IsSimpleModule Aᵐᵒᵖ
      (fiberKernelRightSocleSubmodule Y Z Top f g hZkill) := by
    letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z) :=
      hZsimple
    exact IsSimpleModule.congr
      (LinearEquiv.ofInjective
        (fiberKernelRightSocleMap Y Z Top f g hZkill)
        (fiberKernelRightSocleMap_injective Y Z Top f g hZkill)).symm
  rcases hside with hleft | hright
  · have hly : fiberKernelLeftSocleMap Y Z Top f g hYkill y ∈ P :=
      hleft ⟨y, rfl⟩
    have hrz : fiberKernelRightSocleMap Y Z Top f g hZkill z ∈ P := by
      have := P.sub_mem hmixed hly
      simpa using this
    have hrzNe : fiberKernelRightSocleMap Y Z Top f g hZkill z ≠ 0 := by
      intro hzero
      apply hz
      exact fiberKernelRightSocleMap_injective Y Z Top f g hZkill (by simpa using hzero)
    have hinf : fiberKernelRightSocleSubmodule Y Z Top f g hZkill ⊓ P ≠ ⊥ := by
      intro hbot
      have hmem : fiberKernelRightSocleMap Y Z Top f g hZkill z ∈
          fiberKernelRightSocleSubmodule Y Z Top f g hZkill ⊓ P :=
        ⟨⟨z, rfl⟩, hrz⟩
      have hzero : fiberKernelRightSocleMap Y Z Top f g hZkill z = 0 := by
        simpa [hbot] using hmem
      exact hrzNe hzero
    have hrightLe : fiberKernelRightSocleSubmodule Y Z Top f g hZkill ≤ P := by
      have hatom : IsAtom (fiberKernelRightSocleSubmodule Y Z Top f g hZkill) :=
        isSimpleModule_iff_isAtom.mp hrightSimple
      have heq : fiberKernelRightSocleSubmodule Y Z Top f g hZkill ⊓ P =
          fiberKernelRightSocleSubmodule Y Z Top f g hZkill :=
        (hatom.le_iff_eq hinf).mp inf_le_left
      rw [← heq]
      exact inf_le_right
    exact moduleSocle_fiberKernel_le_of_coordinateSocles_le
      Y Z Top f g hYsimple hZsimple hYkill hZkill P hleft hrightLe
  · have hrz : fiberKernelRightSocleMap Y Z Top f g hZkill z ∈ P :=
      hright ⟨z, rfl⟩
    have hly : fiberKernelLeftSocleMap Y Z Top f g hYkill y ∈ P := by
      have := P.sub_mem hmixed hrz
      simpa [add_sub_cancel_right] using this
    have hlyNe : fiberKernelLeftSocleMap Y Z Top f g hYkill y ≠ 0 := by
      intro hzero
      apply hy
      exact fiberKernelLeftSocleMap_injective Y Z Top f g hYkill (by simpa using hzero)
    have hinf : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ⊓ P ≠ ⊥ := by
      intro hbot
      have hmem : fiberKernelLeftSocleMap Y Z Top f g hYkill y ∈
          fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ⊓ P :=
        ⟨⟨y, rfl⟩, hly⟩
      have hzero : fiberKernelLeftSocleMap Y Z Top f g hYkill y = 0 := by
        simpa [hbot] using hmem
      exact hlyNe hzero
    have hleftLe : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ≤ P := by
      have hatom : IsAtom (fiberKernelLeftSocleSubmodule Y Z Top f g hYkill) :=
        isSimpleModule_iff_isAtom.mp hleftSimple
      have heq : fiberKernelLeftSocleSubmodule Y Z Top f g hYkill ⊓ P =
          fiberKernelLeftSocleSubmodule Y Z Top f g hYkill :=
        (hatom.le_iff_eq hinf).mp inf_le_left
      rw [← heq]
      exact inf_le_right
    exact moduleSocle_fiberKernel_le_of_coordinateSocles_le
      Y Z Top f g hYsimple hZsimple hYkill hZkill P hleftLe hright

/-- For non-isomorphic simple branch socles, a mixed vector with two nonzero
socle coordinates already forces a nonzero submodule with simple socle to
contain the whole fiber-kernel socle. -/
theorem moduleSocle_fiberKernel_le_of_mixed_of_nonisomorphic
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hnoniso : ¬ Nonempty
      (moduleSocle Aᵐᵒᵖ Y ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    [IsArtinian Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)]
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (hPsocleSimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ P))
    (y : moduleSocle Aᵐᵒᵖ Y) (z : moduleSocle Aᵐᵒᵖ Z)
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hmixed : fiberKernelLeftSocleMap Y Z Top f g hYkill y +
      fiberKernelRightSocleMap Y Z Top f g hZkill z ∈ P) :
    moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) ≤ P :=
  moduleSocle_fiberKernel_le_of_mixed_of_coordinate_le
    Y Z Top f g hYsimple hZsimple hYkill hZkill P y z hy hz hmixed
      (fiberKernel_coordinateSocle_le_of_simpleSocle
        Y Z Top f g hYsimple hZsimple hnoniso hYkill hZkill
          P hPsocleSimple)

/-- The coordinate-free mixed-vector predicate supplies the concrete sum of
the two coordinate socle embeddings used by the capture theorem. -/
theorem moduleSocle_fiberKernel_le_of_hasMixed_of_nonisomorphic
    (Y Z Top : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] Top) (g : Z →ₗ[Aᵐᵒᵖ] Top)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hnoniso : ¬ Nonempty
      (moduleSocle Aᵐᵒᵖ Y ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    [IsArtinian Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g)]
    (P : Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g))
    (hPsocleSimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ P))
    (hmixed : HasMixedSocleCoordinates Y Z Top f g P) :
    moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z Top f g) ≤ P := by
  obtain ⟨y, z, hy, hz, w, hw, hwcoord⟩ := hmixed
  have hsum : fiberKernelLeftSocleMap Y Z Top f g hYkill y +
      fiberKernelRightSocleMap Y Z Top f g hZkill z = w := by
    apply fiberKernelInclusion_injective Y Z Top f g
    rw [map_add, fiberKernelInclusion_leftSocleMap,
      fiberKernelInclusion_rightSocleMap, hwcoord]
    apply Prod.ext <;> simp
  apply moduleSocle_fiberKernel_le_of_mixed_of_nonisomorphic
    Y Z Top f g hYsimple hZsimple hnoniso hYkill hZkill
      P hPsocleSimple y z hy hz
  rwa [hsum]

end MagnitudeConjecture.RightModule
