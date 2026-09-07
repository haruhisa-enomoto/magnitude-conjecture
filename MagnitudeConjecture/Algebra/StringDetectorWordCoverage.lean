import MagnitudeConjecture.Algebra.StringDetectorFiniteIndex
import MagnitudeConjecture.Algebra.StringDetectorWordOrder
import MagnitudeConjecture.LinearAlgebra.FiniteFiltration

/-!
# Coverage by finite endpoint-word intervals

Besides its lower and upper boundary subspaces, an endpoint word transports
the zero and whole source spaces.  A vector lying in the transported whole
space but outside the transported zero space can be followed down the finite
source-extension tree: membership in the lower boundary forces the positive
child, while failure of membership in the upper boundary forces the inverse
child.  Both moves preserve the invariant and strictly increase word length.
The uniform finite-word bound therefore forces the process to stop inside an
actual word interval.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u : Q} {t : Bool}

namespace EndpointWord

/-- Transport of the zero source subspace along an endpoint word. -/
def zeroSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u))) :=
  signedPathSubspace N C.path ⊥

/-- Transport of the whole source space along an endpoint word. -/
def wholeSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u))) :=
  signedPathSubspace N C.path ⊤

theorem zeroSubspace_le_lowerSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    zeroSubspace N C ≤ lowerSubspace N C := by
  exact signedPathSubspace_mono N C.path bot_le

theorem upperSubspace_le_wholeSubspace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) :
    upperSubspace N C ≤ wholeSubspace N C := by
  exact signedPathSubspace_mono N C.path le_top

/-- With no positive source extension, the lower endpoint is the transported
zero space. -/
theorem lowerSubspace_eq_zeroSubspace_of_not_nonempty_incomingExtension
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (hinc : ¬ Nonempty C.IncomingExtension) :
    lowerSubspace N C = zeroSubspace N C := by
  simp [lowerSubspace, lowerBoundarySubspace, zeroSubspace, hinc]

/-- With no inverse source extension, the upper endpoint is the transported
whole space. -/
theorem upperSubspace_eq_wholeSubspace_of_not_nonempty_outgoingInverseExtension
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t)
    (hout : ¬ Nonempty C.OutgoingInverseExtension) :
    upperSubspace N C = wholeSubspace N C := by
  simp [upperSubspace, upperBoundarySubspace, wholeSubspace, hout]

/-- A positive child has the same transported zero space as its parent. -/
theorem zeroSubspace_prependIncoming
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (inc : C.IncomingExtension) :
    zeroSubspace N (C.prependIncoming inc) = zeroSubspace N C := by
  let a : inc.1.1 ⟶ C.source := inc.1.2
  unfold zeroSubspace
  change signedPathSubspace N ((positiveArrow a).toPath.comp C.path) ⊥ =
    signedPathSubspace N C.path ⊥
  rw [signedPathSubspace_comp, signedPathSubspace_toPath]
  simp

/-- The transported whole space of a positive child is exactly the lower
endpoint of its parent. -/
theorem wholeSubspace_prependIncoming
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (inc : C.IncomingExtension) :
    wholeSubspace N (C.prependIncoming inc) = lowerSubspace N C := by
  classical
  let hinc : Nonempty C.IncomingExtension := ⟨inc⟩
  have hchosen : Classical.choice hinc = inc :=
    @Subsingleton.elim _ C.incomingExtension_subsingleton _ _
  let a : inc.1.1 ⟶ C.source := inc.1.2
  unfold wholeSubspace lowerSubspace
  change signedPathSubspace N ((positiveArrow a).toPath.comp C.path) ⊤ =
    signedPathSubspace N C.path (lowerBoundarySubspace N C)
  rw [signedPathSubspace_comp, signedPathSubspace_toPath]
  apply congrArg (signedPathSubspace N C.path)
  simp only [signedArrowSubspace_positive, lowerBoundarySubspace,
    hinc, dite_true]
  rw [hchosen]

/-- The transported zero space of an inverse child is exactly the upper
endpoint of its parent. -/
theorem zeroSubspace_prependOutgoingInverse
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (out : C.OutgoingInverseExtension) :
    zeroSubspace N (C.prependOutgoingInverse out) = upperSubspace N C := by
  classical
  let hout : Nonempty C.OutgoingInverseExtension := ⟨out⟩
  have hchosen : Classical.choice hout = out :=
    @Subsingleton.elim _ C.outgoingInverseExtension_subsingleton _ _
  let a : C.source ⟶ out.1.1 := out.1.2
  unfold zeroSubspace upperSubspace
  change signedPathSubspace N ((negativeArrow a).toPath.comp C.path) ⊥ =
    signedPathSubspace N C.path (upperBoundarySubspace N C)
  rw [signedPathSubspace_comp, signedPathSubspace_toPath]
  apply congrArg (signedPathSubspace N C.path)
  simp only [signedArrowSubspace_negative, upperBoundarySubspace,
    hout, dite_true]
  rw [hchosen]

/-- An inverse child has the same transported whole space as its parent. -/
theorem wholeSubspace_prependOutgoingInverse
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t) (out : C.OutgoingInverseExtension) :
    wholeSubspace N (C.prependOutgoingInverse out) = wholeSubspace N C := by
  let a : C.source ⟶ out.1.1 := out.1.2
  unfold wholeSubspace
  change signedPathSubspace N ((negativeArrow a).toPath.comp C.path) ⊤ =
    signedPathSubspace N C.path ⊤
  rw [signedPathSubspace_comp, signedPathSubspace_toPath]
  simp

/-- Starting from a word whose transported whole space contains `x` but
whose transported zero space does not, finite word length forces `x` into
one of its source-extension descendant intervals.  The returned prefix is
the certificate that the terminal word really descends from the initial
one. -/
theorem exists_descendant_mem_upperSubspace_not_mem_lowerSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t)
    (x : N.obj (Opposite.op (obj P.toPresentation.relations u)))
    (hxWhole : x ∈ wholeSubspace N C)
    (hxZero : x ∉ zeroSubspace N C) :
    ∃ (D : EndpointWord S u t) (pref : SignedPath D.source C.source),
      D.path = pref.comp C.path ∧
        x ∈ upperSubspace N D ∧ x ∉ lowerSubspace N D := by
  obtain ⟨L, hL⟩ :=
    DetectorIndex.exists_word_length_bound_of_finite_detectorIndex
      (P := P) (S := S)
  have hCL : C.word.length ≤ L := hL C.word
  induction hgap : L - C.word.length using Nat.strong_induction_on
      generalizing C with
  | h gap ih =>
      by_cases hxLower : x ∈ lowerSubspace N C
      · have hinc : Nonempty C.IncomingExtension := by
          by_contra hnone
          apply hxZero
          rw [← lowerSubspace_eq_zeroSubspace_of_not_nonempty_incomingExtension
            N C hnone]
          exact hxLower
        let inc := Classical.choice hinc
        let D := C.prependIncoming inc
        have hDWhole : x ∈ wholeSubspace N D := by
          rw [wholeSubspace_prependIncoming N C inc]
          exact hxLower
        have hDZero : x ∉ zeroSubspace N D := by
          rw [zeroSubspace_prependIncoming N C inc]
          exact hxZero
        have hDL : D.word.length ≤ L := hL D.word
        have hDLength : D.word.length = C.word.length + 1 := by
          exact prependIncoming_length C inc
        have hgapLT : L - D.word.length < gap := by
          rw [← hgap]
          rw [hDLength]
          omega
        obtain ⟨E, pref, hEpath, hxEUpper, hxENotLower⟩ :=
          ih (L - D.word.length) hgapLT D hDWhole hDZero hDL rfl
        refine ⟨E, pref.comp (positiveArrow inc.1.2).toPath, ?_,
          hxEUpper, hxENotLower⟩
        rw [hEpath, prependIncoming_path, Quiver.Path.comp_assoc]
        rfl
      · by_cases hxUpper : x ∈ upperSubspace N C
        · exact ⟨C, Quiver.Path.nil, by simp, hxUpper, hxLower⟩
        · have hout : Nonempty C.OutgoingInverseExtension := by
            by_contra hnone
            apply hxUpper
            rw [upperSubspace_eq_wholeSubspace_of_not_nonempty_outgoingInverseExtension
              N C hnone]
            exact hxWhole
          let out := Classical.choice hout
          let D := C.prependOutgoingInverse out
          have hDWhole : x ∈ wholeSubspace N D := by
            rw [wholeSubspace_prependOutgoingInverse N C out]
            exact hxWhole
          have hDZero : x ∉ zeroSubspace N D := by
            rw [zeroSubspace_prependOutgoingInverse N C out]
            exact hxUpper
          have hDL : D.word.length ≤ L := hL D.word
          have hDLength : D.word.length = C.word.length + 1 := by
            exact prependOutgoingInverse_length C out
          have hgapLT : L - D.word.length < gap := by
            rw [← hgap]
            rw [hDLength]
            omega
          obtain ⟨E, pref, hEpath, hxEUpper, hxENotLower⟩ :=
            ih (L - D.word.length) hgapLT D hDWhole hDZero hDL rfl
          refine ⟨E, pref.comp (negativeArrow out.1.2).toPath, ?_,
            hxEUpper, hxENotLower⟩
          rw [hEpath, prependOutgoingInverse_path, Quiver.Path.comp_assoc]
          rfl

/-- The descendant certificate may be forgotten when only interval coverage
is needed. -/
theorem exists_mem_upperSubspace_not_mem_lowerSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u t)
    (x : N.obj (Opposite.op (obj P.toPresentation.relations u)))
    (hxWhole : x ∈ wholeSubspace N C)
    (hxZero : x ∉ zeroSubspace N C) :
    ∃ D : EndpointWord S u t,
      x ∈ upperSubspace N D ∧ x ∉ lowerSubspace N D := by
  obtain ⟨D, _, _, hxUpper, hxLower⟩ :=
    exists_descendant_mem_upperSubspace_not_mem_lowerSubspace
      N C x hxWhole hxZero
  exact ⟨D, hxUpper, hxLower⟩

/-- Every nonzero vector at a displayed vertex lies in the upper but not the
lower subspace of some endpoint word of either fixed polarization. -/
theorem exists_endpointWord_interval_of_ne_zero
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (u : Q) (t : Bool)
    (x : N.obj (Opposite.op (obj P.toPresentation.relations u)))
    (hx : x ≠ 0) :
    ∃ C : EndpointWord S u t,
      x ∈ upperSubspace N C ∧ x ∉ lowerSubspace N C := by
  let C := EndpointWord.vertex P S u t
  apply exists_mem_upperSubspace_not_mem_lowerSubspace N C x
  · change x ∈ signedPathSubspace N
      (Quiver.Path.nil : SignedPath u u) ⊤
    simp
  · change x ∉ signedPathSubspace N
      (Quiver.Path.nil : SignedPath u u) ⊥
    simpa using hx

/-- The finite endpoint-word family in its canonical in-order enumeration. -/
noncomputable def orderedWordOrderIso [Finite (DetectorIndex S)] :
    Fin (Nat.card (EndpointWord S u t)) ≃o EndpointWord S u t := by
  letI : Finite (EndpointWord S u t) :=
    DetectorIndex.finite_endpointWord_of_finite_detectorIndex
      (P := P) (S := S) u t
  letI : Fintype (EndpointWord S u t) := Fintype.ofFinite _
  have hcard : (Finset.univ : Finset (EndpointWord S u t)).card =
      Nat.card (EndpointWord S u t) := by
    simp [Nat.card_eq_fintype_card]
  let e := (Finset.univ : Finset (EndpointWord S u t)).orderIsoOfFin hcard
  exact e.trans {
    toFun := fun C ↦ C.1
    invFun := fun C ↦ ⟨C, Finset.mem_univ C⟩
    left_inv := fun C ↦ Subtype.ext rfl
    right_inv := fun C ↦ rfl
    map_rel_iff' := by intro C D; rfl }

/-- The `i`th endpoint word in canonical in-order enumeration. -/
noncomputable def orderedWord [Finite (DetectorIndex S)]
    (i : Fin (Nat.card (EndpointWord S u t))) : EndpointWord S u t :=
  orderedWordOrderIso (P := P) (S := S) (u := u) (t := t) i

theorem orderedWord_lt_iff [Finite (DetectorIndex S)]
    {i j : Fin (Nat.card (EndpointWord S u t))} :
    orderedWord (P := P) (S := S) i < orderedWord (P := P) (S := S) j ↔
      i < j :=
  (orderedWordOrderIso (P := P) (S := S) (u := u) (t := t)).lt_iff_lt

theorem orderedWord_surjective [Finite (DetectorIndex S)] :
    Function.Surjective
      (orderedWord (P := P) (S := S) (u := u) (t := t)) :=
  (orderedWordOrderIso (P := P) (S := S) (u := u) (t := t)).surjective

/-- Upper endpoints of earlier canonical words lie below the lower endpoint
of every later word. -/
theorem orderedWord_upperSubspace_le_lowerSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {i j : Fin (Nat.card (EndpointWord S u t))} (hij : i < j) :
    upperSubspace N (orderedWord (P := P) (S := S) i) ≤
      lowerSubspace N (orderedWord (P := P) (S := S) j) := by
  apply upperSubspace_le_lowerSubspace_of_wordLT
  rw [wordLT_iff_lt, orderedWord_lt_iff]
  exact hij

/-- Cumulative upper endpoints before the cut `j` in the finite word order. -/
noncomputable def cumulativeWordSubspace [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (j : Fin (Nat.card (EndpointWord S u t) + 1)) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u))) :=
  ⨆ (i : Fin (Nat.card (EndpointWord S u t))),
    ⨆ (_ : i.val < j.val),
      upperSubspace N (orderedWord (P := P) (S := S) i)

/-- Before the `j`th word, the cumulative upper endpoints lie in its lower
endpoint. -/
theorem cumulativeWordSubspace_le_lowerSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (EndpointWord S u t))) :
    cumulativeWordSubspace (P := P) (S := S) N j.castSucc ≤
      lowerSubspace N (orderedWord (P := P) (S := S) j) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hij
  exact orderedWord_upperSubspace_le_lowerSubspace N hij

/-- Coverage and avoidance leave no gap before any word interval. -/
theorem lowerSubspace_le_cumulativeWordSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (EndpointWord S u t))) :
    lowerSubspace N (orderedWord (P := P) (S := S) j) ≤
      cumulativeWordSubspace (P := P) (S := S) N j.castSucc := by
  intro x hxLower
  by_cases hxZero : x = 0
  · subst x
    exact Submodule.zero_mem _
  obtain ⟨D, hxUpperD, hxNotLowerD⟩ :=
    exists_endpointWord_interval_of_ne_zero
      (P := P) (S := S) N u t x hxZero
  obtain ⟨d, rfl⟩ := orderedWord_surjective
    (P := P) (S := S) (u := u) (t := t) D
  rcases lt_trichotomy d j with hdj | hdj | hjd
  · apply Submodule.mem_iSup_of_mem d
    exact Submodule.mem_iSup_of_mem hdj hxUpperD
  · subst d
    exact (hxNotLowerD hxLower).elim
  · apply (hxNotLowerD ?_).elim
    apply orderedWord_upperSubspace_le_lowerSubspace N hjd
    apply lowerSubspace_le_upperSubspace N
    exact hxLower

/-- The cumulative cut immediately before a word is exactly its lower
endpoint. -/
theorem cumulativeWordSubspace_castSucc
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (EndpointWord S u t))) :
    cumulativeWordSubspace (P := P) (S := S) N j.castSucc =
      lowerSubspace N (orderedWord (P := P) (S := S) j) :=
  le_antisymm (cumulativeWordSubspace_le_lowerSubspace N j)
    (lowerSubspace_le_cumulativeWordSubspace N j)

/-- Adding the `j`th upper endpoint makes the cumulative cut exactly that
upper endpoint. -/
theorem cumulativeWordSubspace_succ
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (EndpointWord S u t))) :
    cumulativeWordSubspace (P := P) (S := S) N j.succ =
      upperSubspace N (orderedWord (P := P) (S := S) j) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hij
    have hijVal : i.val < j.val + 1 := by
      simpa only [Fin.val_succ] using hij
    have hij' : i ≤ j := by omega
    rcases hij'.lt_or_eq with hij' | rfl
    · exact (orderedWord_upperSubspace_le_lowerSubspace N hij').trans
        (lowerSubspace_le_upperSubspace N _)
    · exact le_rfl
  · apply le_iSup_of_le j
    apply le_iSup_of_le (show j.val < j.succ.val by
      simpa only [Fin.val_succ] using Nat.lt_succ_self j.val)
    exact le_rfl

/-- The initial cumulative word cut is zero. -/
theorem cumulativeWordSubspace_zero
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k) :
    cumulativeWordSubspace (P := P) (S := S) (u := u) (t := t) N 0 =
      (⊥ : Submodule k (N.obj (Opposite.op
        (obj P.toPresentation.relations u)))) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    have hi' : i.val < 0 := by
      simpa only [Fin.val_zero] using hi
    omega
  · exact bot_le

/-- Coverage makes the final cumulative word cut the whole vertex space. -/
theorem cumulativeWordSubspace_last
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k) :
    cumulativeWordSubspace (P := P) (S := S) N
        (Fin.last (Nat.card (EndpointWord S u t))) = ⊤ := by
  apply top_unique
  intro x hx
  by_cases hxZero : x = 0
  · subst x
    exact Submodule.zero_mem _
  obtain ⟨D, hxUpperD, hxNotLowerD⟩ :=
    exists_endpointWord_interval_of_ne_zero
      (P := P) (S := S) N u t x hxZero
  obtain ⟨d, rfl⟩ := orderedWord_surjective
    (P := P) (S := S) (u := u) (t := t) D
  apply Submodule.mem_iSup_of_mem d
  exact Submodule.mem_iSup_of_mem d.isLt hxUpperD

/-- The canonical finite filtration supplied by one endpoint polarization. -/
noncomputable def orderedWordFiltration [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] :
    MagnitudeConjecture.LinearAlgebra.FiniteFiltration.Filtration k
      (N.obj (Opposite.op (obj P.toPresentation.relations u)))
      (Nat.card (EndpointWord S u t)) where
  subspace := cumulativeWordSubspace (P := P) (S := S) N
  monotone_subspace := by
    intro i j hij
    apply iSup_le
    intro w
    apply iSup_le
    intro hwi
    apply le_iSup_of_le w
    apply le_iSup_of_le (lt_of_lt_of_le hwi hij)
    exact le_rfl
  subspace_zero := cumulativeWordSubspace_zero
    (P := P) (S := S) (u := u) (t := t) N
  subspace_last := cumulativeWordSubspace_last
    (P := P) (S := S) (u := u) (t := t) N

/-- Every module morphism preserves the canonical polarized word
filtrations. -/
theorem orderedWordFiltration_compatible
    [Finite (DetectorIndex S)]
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N) :
    MagnitudeConjecture.LinearAlgebra.FiniteFiltration.Filtration.Compatible
      (f.app (Opposite.op (obj P.toPresentation.relations u))).hom
      (orderedWordFiltration (P := P) (S := S) (t := t) M)
      (orderedWordFiltration (P := P) (S := S) (t := t) N) := by
  intro j
  change (cumulativeWordSubspace (P := P) (S := S) (t := t) M j).map
      (f.app (Opposite.op (obj P.toPresentation.relations u))).hom ≤
    cumulativeWordSubspace (P := P) (S := S) (t := t) N j
  rw [cumulativeWordSubspace, Submodule.map_iSup]
  apply iSup_le
  intro i
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hij
  apply le_iSup_of_le i
  apply le_iSup_of_le hij
  exact upperSubspace_map_le f _

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
