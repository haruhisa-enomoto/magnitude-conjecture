import MagnitudeConjecture.Algebra.StringQuotientEndLocal
import MagnitudeConjecture.Algebra.StringArrowRightIdealBasis

/-!
# Skeletality of a string bound-quiver quotient

The positive-length path filtration is closed under composition.  A morphism
between distinct displayed vertices lies in its first step, whereas the
identity does not.  Thus two distinct displayed vertices cannot become
isomorphic in the quotient category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The subspace of a quotient Hom space spanned by surviving paths of length
at least `n`.  The endpoint order follows the quotient category's
contravariant path convention. -/
def quotientHomLengthTail
    (P : StringPresentation k A Q) (x y : Q) (n : ℕ) :
    Submodule k
      (obj P.toPresentation.relations y ⟶
        obj P.toPresentation.relations x) :=
  Submodule.span k
    (survivingPathBasis P.toPresentation.relations P.monomial x y ''
      {p | n ≤ p.1.length})

/-- A displayed arrow, regarded as a surviving path of length one. -/
def survivingArrowPath
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    SurvivingPath P.toPresentation.relations x y :=
  ⟨a.toPath, pathMap_ne_zero_of_length_lt_two
    P.toPresentation.admissible a.toPath (by simp)⟩

@[simp]
theorem survivingArrowPath_length
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (P.survivingArrowPath a).1.length = 1 := by
  simp [survivingArrowPath]

@[simp]
theorem survivingPathBasis_survivingArrowPath
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    survivingPathBasis P.toPresentation.relations P.monomial x y
        (P.survivingArrowPath a) =
      arrowMap P.toPresentation.relations a := by
  simp [survivingArrowPath, arrowMap]

/-- A surviving-path basis vector belongs to every Hom tail below its path
length. -/
theorem survivingPathBasis_mem_quotientHomLengthTail
    (P : StringPresentation k A Q) (x y : Q) (n : ℕ)
    (p : SurvivingPath P.toPresentation.relations x y)
    (hp : n ≤ p.1.length) :
    survivingPathBasis P.toPresentation.relations P.monomial x y p ∈
      P.quotientHomLengthTail x y n := by
  apply Submodule.subset_span
  exact ⟨p, hp, rfl⟩

/-- Between distinct displayed vertices, every quotient morphism has positive
path length. -/
theorem quotientHomLengthTail_one_eq_top_of_ne
    (P : StringPresentation k A Q) {x y : Q} (hxy : x ≠ y) :
    P.quotientHomLengthTail x y 1 = ⊤ := by
  apply top_unique
  let b := survivingPathBasis
    P.toPresentation.relations P.monomial x y
  have hspan : Submodule.span k (Set.range b) ≤
      P.quotientHomLengthTail x y 1 := by
    apply Submodule.span_le.2
    rintro _ ⟨p, rfl⟩
    apply P.survivingPathBasis_mem_quotientHomLengthTail x y 1 p
    apply Nat.one_le_iff_ne_zero.2
    intro hp
    exact hxy (Quiver.Path.eq_of_length_zero p.1 hp)
  simpa only [b.span_eq] using hspan

/-- The quotient Hom path filtration is decreasing. -/
theorem quotientHomLengthTail_antitone
    (P : StringPresentation k A Q) (x y : Q) {m n : ℕ}
    (hmn : m ≤ n) :
    P.quotientHomLengthTail x y n ≤
      P.quotientHomLengthTail x y m := by
  apply Submodule.span_mono
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hmn.trans hp, rfl⟩

/-- Composition adds lower bounds in the quotient Hom path filtration. -/
theorem comp_mem_quotientHomLengthTail
    (P : StringPresentation k A Q) {x y z : Q} {i j : ℕ}
    {f : obj P.toPresentation.relations y ⟶
      obj P.toPresentation.relations x}
    {g : obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations y}
    (hf : f ∈ P.quotientHomLengthTail x y i)
    (hg : g ∈ P.quotientHomLengthTail y z j) :
    g ≫ f ∈ P.quotientHomLengthTail x z (i + j) := by
  let T := P.quotientHomLengthTail x z (i + j)
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, hq, rfl⟩ := hg
          rw [survivingPathBasis_apply, survivingPathBasis_apply]
          rw [pathMap_comp]
          by_cases hzero :
              pathMap P.toPresentation.relations (p.1.comp q.1) = 0
          · rw [hzero]
            exact Submodule.zero_mem _
          · let r : SurvivingPath P.toPresentation.relations x z :=
              ⟨p.1.comp q.1, hzero⟩
            rw [← survivingPathBasis_apply
              P.toPresentation.relations P.monomial x z r]
            apply P.survivingPathBasis_mem_quotientHomLengthTail
            change i + j ≤ (p.1.comp q.1).length
            simpa [Quiver.Path.length_comp] using Nat.add_le_add hp hq
      | zero => simp
      | add g h _ _ hgm hhm =>
          simpa [Preadditive.add_comp] using T.add_mem hgm hhm
      | smul c g _ hgm =>
          simpa using T.smul_mem c hgm
  | zero => simp
  | add f h _ _ hfm hhm =>
      simpa [Preadditive.comp_add] using T.add_mem hfm hhm
  | smul c f _ hfm =>
      simpa using T.smul_mem c hfm

/-- Two distinct displayed arrows remain linearly distinct modulo the
length-two path tail. -/
theorem smul_arrowMap_sub_smul_arrowMap_not_mem_lengthTail_two
    (P : StringPresentation k A Q) {x y : Q} {a b : x ⟶ y}
    (hab : a ≠ b) {c d : k} (hc : c ≠ 0) :
    c • arrowMap P.toPresentation.relations a -
        d • arrowMap P.toPresentation.relations b ∉
      P.quotientHomLengthTail x y 2 := by
  intro htail
  let B := survivingPathBasis P.toPresentation.relations P.monomial x y
  let pa := P.survivingArrowPath a
  let pb := P.survivingArrowPath b
  have hpab : pa ≠ pb := by
    intro h
    apply hab
    apply eq_of_heq
    exact Quiver.Path.hom_heq_of_cons_eq_cons (congrArg Subtype.val h)
  have hsupport :
      (↑(B.repr
        (c • arrowMap P.toPresentation.relations a -
          d • arrowMap P.toPresentation.relations b)).support :
          Set (SurvivingPath P.toPresentation.relations x y)) ⊆
        {p : SurvivingPath P.toPresentation.relations x y |
          2 ≤ p.1.length} := by
    rw [quotientHomLengthTail, B.mem_span_image] at htail
    exact htail
  have hnotmem : pa ∉
      (B.repr
        (c • arrowMap P.toPresentation.relations a -
          d • arrowMap P.toPresentation.relations b)).support := by
    intro hmem
    have hlength := hsupport hmem
    change 2 ≤ pa.1.length at hlength
    simp [pa, survivingArrowPath] at hlength
  have hcoeff :
      B.repr
          (c • arrowMap P.toPresentation.relations a -
            d • arrowMap P.toPresentation.relations b) pa = 0 :=
    Finsupp.notMem_support_iff.mp hnotmem
  have hreprA :
      B.repr (arrowMap P.toPresentation.relations a) =
        Finsupp.single pa 1 := by
    rw [← P.survivingPathBasis_survivingArrowPath a]
    exact B.repr_self pa
  have hreprB :
      B.repr (arrowMap P.toPresentation.relations b) =
        Finsupp.single pb 1 := by
    rw [← P.survivingPathBasis_survivingArrowPath b]
    exact B.repr_self pb
  rw [map_sub, map_smul, map_smul, hreprA, hreprB] at hcoeff
  have hcZero : c = 0 := by
    simpa [Finsupp.single_apply, hpab] using hcoeff
  exact hc hcZero

/-- On an endomorphism space, the Hom path tail is the previously defined
endomorphism-ring path tail. -/
theorem quotientHomLengthTail_self_eq_quotientVertexEndLengthTail
    (P : StringPresentation k A Q) (x : Q) (n : ℕ) :
    P.quotientHomLengthTail x x n =
      P.quotientVertexEndLengthTail x n := by
  unfold quotientHomLengthTail quotientVertexEndLengthTail
  congr 1

/-- The identity of a displayed quotient vertex does not have positive path
length. -/
theorem quotientIdentity_not_mem_quotientHomLengthTail_one
    (P : StringPresentation k A Q) (x : Q) :
    𝟙 (obj P.toPresentation.relations x) ∉
      P.quotientHomLengthTail x x 1 := by
  rw [P.quotientHomLengthTail_self_eq_quotientVertexEndLengthTail x 1]
  intro h
  letI : IsLocalRing
      (End (obj P.toPresentation.relations x)) :=
    P.quotientVertexEnd_isLocalRing x
  have hnil : IsNilpotent
      (1 : End (obj P.toPresentation.relations x)) :=
    P.isNilpotent_of_mem_quotientVertexEndLengthTail_one x 1 h
  exact not_isNilpotent_one hnil

/-- The scalar part of an invertible vertex endomorphism is nonzero. -/
theorem scalar_ne_zero_of_isIso_of_eq_smul_one_add_tail
    (P : StringPresentation k A Q) (y : Q)
    (f : End (obj P.toPresentation.relations y)) [IsIso f]
    {c : k} {r : End (obj P.toPresentation.relations y)}
    (hr : r ∈ P.quotientVertexEndLengthTail y 1)
    (hfr : f = c • 1 + r) :
    c ≠ 0 := by
  letI : Nontrivial (End (obj P.toPresentation.relations y)) :=
    P.quotientVertexEnd_nontrivial y
  intro hc
  subst c
  have hf : f = r := by simpa using hfr
  have hnil : IsNilpotent f := by
    rw [hf]
    exact P.isNilpotent_of_mem_quotientVertexEndLengthTail_one y r hr
  exact hnil.not_isUnit
    ((CategoryTheory.isUnit_iff_isIso f).2 inferInstance)

/-- A commuting square with invertible vertex endomorphisms cannot identify
two distinct displayed arrows. -/
theorem arrow_eq_of_iso_square
    (P : StringPresentation k A Q) {x y : Q} (a b : x ⟶ y)
    (ex : obj P.toPresentation.relations x ≅
      obj P.toPresentation.relations x)
    (ey : obj P.toPresentation.relations y ≅
      obj P.toPresentation.relations y)
    (hcomm :
      arrowMap P.toPresentation.relations a ≫ ex.hom =
        ey.hom ≫ arrowMap P.toPresentation.relations b) :
    a = b := by
  by_contra hab
  obtain ⟨c, rx, hrx, hex⟩ :=
    P.exists_eq_smul_one_add_mem_quotientVertexEndLengthTail_one x ex.hom
  obtain ⟨d, ry, hry, hey⟩ :=
    P.exists_eq_smul_one_add_mem_quotientVertexEndLengthTail_one y ey.hom
  have hc : c ≠ 0 :=
    P.scalar_ne_zero_of_isIso_of_eq_smul_one_add_tail x ex.hom hrx hex
  have haTail : arrowMap P.toPresentation.relations a ∈
      P.quotientHomLengthTail x y 1 := by
    rw [← P.survivingPathBasis_survivingArrowPath a]
    exact P.survivingPathBasis_mem_quotientHomLengthTail x y 1
      (P.survivingArrowPath a) (by simp)
  have hbTail : arrowMap P.toPresentation.relations b ∈
      P.quotientHomLengthTail x y 1 := by
    rw [← P.survivingPathBasis_survivingArrowPath b]
    exact P.survivingPathBasis_mem_quotientHomLengthTail x y 1
      (P.survivingArrowPath b) (by simp)
  have hax : arrowMap P.toPresentation.relations a ≫ rx ∈
      P.quotientHomLengthTail x y 2 := by
    simpa using P.comp_mem_quotientHomLengthTail hrx haTail
  have hyb : ry ≫ arrowMap P.toPresentation.relations b ∈
      P.quotientHomLengthTail x y 2 := by
    simpa using P.comp_mem_quotientHomLengthTail hbTail hry
  have hlead :
      c • arrowMap P.toPresentation.relations a -
          d • arrowMap P.toPresentation.relations b =
        ry ≫ arrowMap P.toPresentation.relations b -
          arrowMap P.toPresentation.relations a ≫ rx := by
    have hexHom : ex.hom =
        c • 𝟙 (obj P.toPresentation.relations x) + End.asHom rx := by
      exact congrArg End.asHom hex
    have heyHom : ey.hom =
        d • 𝟙 (obj P.toPresentation.relations y) + End.asHom ry := by
      exact congrArg End.asHom hey
    rw [hexHom, heyHom] at hcomm
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp] at hcomm
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      simpa only [add_comm] using hcomm)
  apply P.smul_arrowMap_sub_smul_arrowMap_not_mem_lengthTail_two hab hc
  rw [hlead]
  exact Submodule.sub_mem _ hyb hax

/-- Isomorphic displayed vertices of a string quotient are equal. -/
theorem eq_of_quotientVertex_iso
    (P : StringPresentation k A Q) {x y : Q}
    (e : obj P.toPresentation.relations x ≅
      obj P.toPresentation.relations y) :
    x = y := by
  by_contra hxy
  have hhom : e.hom ∈ P.quotientHomLengthTail y x 1 := by
    rw [P.quotientHomLengthTail_one_eq_top_of_ne (Ne.symm hxy)]
    exact Submodule.mem_top
  have hinv : e.inv ∈ P.quotientHomLengthTail x y 1 := by
    rw [P.quotientHomLengthTail_one_eq_top_of_ne hxy]
    exact Submodule.mem_top
  have hcomp := P.comp_mem_quotientHomLengthTail hinv hhom
  have hpositive : e.hom ≫ e.inv ∈
      P.quotientHomLengthTail x x 1 :=
    P.quotientHomLengthTail_antitone x x (by omega) hcomp
  rw [e.hom_inv_id] at hpositive
  exact P.quotientIdentity_not_mem_quotientHomLengthTail_one x hpositive

/-- The quotient category of a string presentation is skeletal. -/
theorem quotientCategory_skeletal
    (P : StringPresentation k A Q) :
    Skeletal (Category P.toPresentation.relations) := by
  intro X Y hXY
  obtain ⟨e⟩ := hXY
  let x := P.quotientObjectEquiv X
  let y := P.quotientObjectEquiv Y
  let eX : obj P.toPresentation.relations x ≅ X :=
    eqToIso (P.quotientObjectEquiv.symm_apply_apply X)
  let eY : obj P.toPresentation.relations y ≅ Y :=
    eqToIso (P.quotientObjectEquiv.symm_apply_apply Y)
  have hxy : x = y := P.eq_of_quotientVertex_iso
    (eX.trans (e.trans eY.symm))
  exact P.quotientObjectEquiv.injective hxy

end StringPresentation

end MagnitudeConjecture.BoundQuiver
