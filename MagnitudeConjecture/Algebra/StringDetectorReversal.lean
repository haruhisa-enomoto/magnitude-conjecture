import MagnitudeConjecture.Algebra.StringDetectorPairContext

/-!
# Reversal invariance of finite-string detectors

The finite detector index identifies a string with its formal reverse.  This
file constructs the corresponding natural linear equivalence of detector
spaces.  The proof uses the already formalized change-of-split theorem: at the
source end of a nontrivial word, the complete-word detector is the swapped
pair presentation of the detector of the reversed word.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

private theorem bijective_of_linearEquiv_naturality
    {X Y X' Y' : Type u}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (g : X →ₗ[k] Y) (h : X' →ₗ[k] Y')
    (eX : X ≃ₗ[k] X') (eY : Y ≃ₗ[k] Y')
    (hnatural : ∀ x, eY (g x) = h (eX x))
    (hbijective : Function.Bijective g) :
    Function.Bijective h := by
  constructor
  · intro x₁ x₂ hx
    obtain ⟨q₁, rfl⟩ := eX.surjective x₁
    obtain ⟨q₂, rfl⟩ := eX.surjective x₂
    apply congrArg eX
    apply hbijective.1
    apply eY.injective
    rw [hnatural, hnatural, hx]
  · intro y
    obtain ⟨z, rfl⟩ := eY.surjective y
    obtain ⟨x, hx⟩ := hbijective.2 z
    refine ⟨eX x, ?_⟩
    rw [← hnatural, hx]

/-- View an endpoint word through the canonical double-negation equality of
its target polarization. -/
def doubleNotTarget (C : EndpointWord S u₀ t) :
    EndpointWord S u₀ (Bool.not (Bool.not t)) := by
  cases t <;> exact C

@[simp]
theorem doubleNotTarget_word (C : EndpointWord S u₀ t) :
    (doubleNotTarget C).word = C.word := by
  cases t <;> rfl

@[simp]
theorem doubleNotTarget_source (C : EndpointWord S u₀ t) :
    (doubleNotTarget C).source = C.source := by
  cases t <;> rfl

@[simp]
theorem upperSubspace_doubleNotTarget
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    upperSubspace N (doubleNotTarget C) = upperSubspace N C := by
  cases t <;> rfl

@[simp]
theorem lowerSubspace_doubleNotTarget
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    lowerSubspace N (doubleNotTarget C) = lowerSubspace N C := by
  cases t <;> rfl

/-- The swapped pair presentation at the far endpoint is the detector of the
nontrivial half. -/
def detectorPairSwapEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    PairDetectorSpace N (doubleNotTarget C) C.oppositeVertex ≃ₗ[k]
      DetectorSpace N C :=
  MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq
    (pairDetectorNumerator N (doubleNotTarget C) C.oppositeVertex)
    (detectorNumerator N C)
    (pairDetectorDenominator N (doubleNotTarget C) C.oppositeVertex)
    (detectorDenominator N C)
    (by
      unfold pairDetectorNumerator detectorNumerator
      rw [upperSubspace_doubleNotTarget, inf_comm])
    (by
      unfold pairDetectorDenominator detectorDenominator
      rw [upperSubspace_doubleNotTarget, lowerSubspace_doubleNotTarget,
        inf_comm (upperSubspace N C),
        inf_comm (lowerSubspace N C), sup_comm])

@[simp]
theorem detectorPairSwapEquiv_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t)
    (x : pairDetectorNumerator N (doubleNotTarget C) C.oppositeVertex) :
    detectorPairSwapEquiv N C (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x.1, by
          rw [detectorNumerator]
          have hx : x.1 ∈
              upperSubspace N C ⊓ upperSubspace N C.oppositeVertex := by
            rw [← upperSubspace_doubleNotTarget N C]
            exact x.2
          exact ⟨hx.2, hx.1⟩⟩ : detectorNumerator N C) := by
  exact MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq_apply_mk
    _ _ _ _ _ _ x

/-- Swapping the far-end pair presentation commutes with every module
morphism. -/
theorem detectorPairSwapEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t)
    (q : PairDetectorSpace M (doubleNotTarget C) C.oppositeVertex) :
    detectorPairSwapEquiv N C
        (pairDetectorLinearMap f (doubleNotTarget C) C.oppositeVertex q) =
      detectorLinearMap f C (detectorPairSwapEquiv M C q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [pairDetectorLinearMap_mk, detectorPairSwapEquiv_mk,
        detectorPairSwapEquiv_mk, detectorLinearMap_mk]
      rfl

/-- Naturality in the inverse direction, used to move an ordinary detector
to the swapped pair presentation. -/
theorem detectorPairSwapEquiv_symm_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t)
    (q : DetectorSpace M C) :
    (detectorPairSwapEquiv N C).symm (detectorLinearMap f C q) =
      pairDetectorLinearMap f (doubleNotTarget C) C.oppositeVertex
        ((detectorPairSwapEquiv M C).symm q) := by
  apply (detectorPairSwapEquiv N C).injective
  rw [LinearEquiv.apply_symm_apply, detectorPairSwapEquiv_naturality,
    LinearEquiv.apply_symm_apply]

/-- The two polarized trivial-word detectors at one vertex are naturally
equivalent. -/
def trivialDetectorEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (u₀ : Q) :
    DetectorSpace N (EndpointWord.vertex P S u₀ false) ≃ₗ[k]
      DetectorSpace N (EndpointWord.vertex P S u₀ true) :=
  detectorPairSwapEquiv N (EndpointWord.vertex P S u₀ true)

/-- The trivial-word equivalence commutes with module morphisms. -/
theorem trivialDetectorEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization) (u₀ : Q)
    (q : DetectorSpace M (EndpointWord.vertex P S u₀ false)) :
    trivialDetectorEquiv N S u₀
        (detectorLinearMap f (EndpointWord.vertex P S u₀ false) q) =
      detectorLinearMap f (EndpointWord.vertex P S u₀ true)
        (trivialDetectorEquiv M S u₀ q) := by
  exact detectorPairSwapEquiv_naturality f
    (EndpointWord.vertex P S u₀ true) q

/-- Naturality of the inverse trivial-word equivalence. -/
theorem trivialDetectorEquiv_symm_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization) (u₀ : Q)
    (q : DetectorSpace M (EndpointWord.vertex P S u₀ true)) :
    (trivialDetectorEquiv N S u₀).symm
        (detectorLinearMap f (EndpointWord.vertex P S u₀ true) q) =
      detectorLinearMap f (EndpointWord.vertex P S u₀ false)
        ((trivialDetectorEquiv M S u₀).symm q) := by
  apply (trivialDetectorEquiv N S u₀).injective
  rw [LinearEquiv.apply_symm_apply, trivialDetectorEquiv_naturality,
    LinearEquiv.apply_symm_apply]

/-- Two nontrivial packaged endpoint words with the same literal word are
equal, including their target vertex and polarization indices. -/
theorem detectorWord_eq_of_underlying_eq_of_length_pos
    (C D : DetectorWord S) (hword : C.underlying = D.underlying)
    (hlength : 0 < C.underlying.length) : C = D := by
  rcases C with ⟨u, t, C⟩
  rcases D with ⟨v, s, D⟩
  change C.word = D.word at hword
  change 0 < C.word.length at hlength
  have huv : u = v := congrArg Word.target hword
  subst v
  have hDlength : 0 < D.word.length := by
    rw [← hword]
    exact hlength
  have hCsign : signedPathTargetSignOr S false C.path = t :=
    (signedPathTargetSignOr_eq_of_length_pos C.path hlength false t).trans
      C.targetSign_eq
  have hDsign : signedPathTargetSignOr S false D.path = s :=
    (signedPathTargetSignOr_eq_of_length_pos D.path hDlength false s).trans
      D.targetSign_eq
  have hsigns : signedPathTargetSignOr S false C.path =
      signedPathTargetSignOr S false D.path :=
    congrArg
      (fun E : Word P.toPresentation.relations ↦
        signedPathTargetSignOr S false E.path) hword
  have hts : t = s := hCsign.symm.trans (hsigns.trans hDsign)
  subst s
  have hCD : C = D := EndpointWord.word_injective S hword
  subst D
  rfl

/-- Bijectivity of a detector map depends only on the literal oriented word,
not on the redundant polarization of the trivial word. -/
theorem detectorLinearMap_bijective_of_word_eq
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    {v : Q} {s : Bool} (C : EndpointWord S u₀ t)
    (D : EndpointWord S v s) (hword : C.word = D.word)
    (hbijective : Function.Bijective (detectorLinearMap f C)) :
    Function.Bijective (detectorLinearMap f D) := by
  by_cases hzero : C.word.length = 0
  · have hDzero : D.word.length = 0 := by rw [← hword]; exact hzero
    have huv : u₀ = v := congrArg Word.target hword
    subst v
    have hCeq := C.eq_vertex_of_word_length_eq_zero hzero
    subst C
    have hDeq := D.eq_vertex_of_word_length_eq_zero hDzero
    subst D
    cases t with
    | false =>
        cases s with
        | false => exact hbijective
        | true =>
            exact bijective_of_linearEquiv_naturality
              (detectorLinearMap f (EndpointWord.vertex P S u₀ false))
              (detectorLinearMap f (EndpointWord.vertex P S u₀ true))
              (trivialDetectorEquiv M S u₀)
              (trivialDetectorEquiv N S u₀)
              (trivialDetectorEquiv_naturality f S u₀) hbijective
    | true =>
        cases s with
        | false =>
            exact bijective_of_linearEquiv_naturality
              (detectorLinearMap f (EndpointWord.vertex P S u₀ true))
              (detectorLinearMap f (EndpointWord.vertex P S u₀ false))
              (trivialDetectorEquiv M S u₀).symm
              (trivialDetectorEquiv N S u₀).symm
              (trivialDetectorEquiv_symm_naturality f S u₀) hbijective
        | true => exact hbijective
  · have hlength : 0 < C.word.length := by omega
    have hpack :
        (⟨u₀, t, C⟩ : DetectorWord S) = ⟨v, s, D⟩ :=
      detectorWord_eq_of_underlying_eq_of_length_pos
        ⟨u₀, t, C⟩ ⟨v, s, D⟩ hword hlength
    cases hpack
    exact hbijective

/-- The swapped endpoint pair associated with `C` is always a valid string:
its complete word is the formal reverse of `C.word`. -/
theorem reversePairIsString (C : EndpointWord S u₀ t) :
    IsString P.toPresentation.relations
      (C.oppositeVertex.path.comp (doubleNotTarget C).path.reverse) := by
  cases t with
  | false =>
      change IsString P.toPresentation.relations
        ((Quiver.Path.nil : SignedPath u₀ u₀).comp C.path.reverse)
      simpa only [Quiver.Path.nil_comp] using
        (isString_reverse_iff P.toPresentation.relations C.path).2 C.isString
  | true =>
      change IsString P.toPresentation.relations
        ((Quiver.Path.nil : SignedPath u₀ u₀).comp C.path.reverse)
      simpa only [Quiver.Path.nil_comp] using
        (isString_reverse_iff P.toPresentation.relations C.path).2 C.isString

/-- The complete word obtained from the swapped endpoint pair of `C`. -/
def reversePairWord (C : EndpointWord S u₀ t) :
    Word P.toPresentation.relations :=
  pairWord (doubleNotTarget C) C.oppositeVertex (reversePairIsString C)

@[simp]
theorem reversePairWord_eq (C : EndpointWord S u₀ t) :
    reversePairWord C = C.word.reverse := by
  cases t with
  | false =>
      apply Word.ext
      · change u₀ = u₀
        rfl
      · change C.source = C.source
        rfl
      · apply heq_of_eq
        change (Quiver.Path.nil : SignedPath u₀ u₀).comp C.path.reverse =
          C.path.reverse
        simp
  | true =>
      apply Word.ext
      · change u₀ = u₀
        rfl
      · change C.source = C.source
        rfl
      · apply heq_of_eq
        change (Quiver.Path.nil : SignedPath u₀ u₀).comp C.path.reverse =
          C.path.reverse
        simp

/-- A nontrivial detector is naturally equivalent to the canonical detector
of its reversed literal word. -/
def detectorReversePairEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C : EndpointWord S u₀ t) (hlength : 0 < C.word.length) :
    DetectorSpace N C ≃ₗ[k]
      DetectorSpace N (detectorEndpoint S (reversePairWord C)) :=
  (detectorPairSwapEquiv N C).symm.trans
    (pairDetectorCompleteWordEquiv N
      (doubleNotTarget C) C.oppositeVertex (reversePairIsString C) (by
        change 0 < (reversePairWord C).length
        rw [reversePairWord_eq, Word.reverse_length]
        exact hlength))

/-- Reversal of a nontrivial detector commutes with every module morphism. -/
theorem detectorReversePairEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (C : EndpointWord S u₀ t) (hlength : 0 < C.word.length)
    (q : DetectorSpace M C) :
    detectorReversePairEquiv N C hlength (detectorLinearMap f C q) =
      detectorLinearMap f (detectorEndpoint S (reversePairWord C))
        (detectorReversePairEquiv M C hlength q) := by
  rw [detectorReversePairEquiv, detectorReversePairEquiv,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    detectorPairSwapEquiv_symm_naturality]
  exact pairDetectorCompleteWordEquiv_naturality f
    (doubleNotTarget C) C.oppositeVertex (reversePairIsString C)
    (by
      change 0 < (reversePairWord C).length
      rw [reversePairWord_eq, Word.reverse_length]
      exact hlength) _

/-- Bijectivity transfers from a nontrivial detector to the canonical
detector of its reversed literal word. -/
theorem detectorLinearMap_reversePairWord_bijective
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (C : EndpointWord S u₀ t) (hlength : 0 < C.word.length)
    (hbijective : Function.Bijective (detectorLinearMap f C)) :
    Function.Bijective
      (detectorLinearMap f (detectorEndpoint S (reversePairWord C))) :=
  bijective_of_linearEquiv_naturality
    (detectorLinearMap f C)
    (detectorLinearMap f (detectorEndpoint S (reversePairWord C)))
    (detectorReversePairEquiv M C hlength)
    (detectorReversePairEquiv N C hlength)
    (detectorReversePairEquiv_naturality f C hlength) hbijective

/-- Bijectivity for the chosen representative of every inversion class
implies bijectivity for every literal endpoint word. -/
theorem detectorLinearMap_bijective_of_detectorIndex
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (hdetector : ∀ i : DetectorIndex S,
      Function.Bijective (detectorLinearMap f i.endpointWord))
    {v : Q} {s : Bool} (C : EndpointWord S v s) :
    Function.Bijective (detectorLinearMap f C) := by
  let i := DetectorIndex.ofWord S C.word
  have hi : DetectorIndex.ofWord S i.endpointWord.word =
      DetectorIndex.ofWord S C.word := by
    simpa only [i] using DetectorIndex.ofWord_endpointWord i
  rcases (DetectorIndex.ofWord_eq_iff S i.endpointWord.word C.word).mp hi with
    hsame | hreverse
  · exact detectorLinearMap_bijective_of_word_eq
      f i.endpointWord C hsame (hdetector i)
  · by_cases hzero : i.endpointWord.word.length = 0
    · have hCzero : C.word.length = 0 := by
        have hlength := congrArg
          (fun E : Word P.toPresentation.relations ↦ E.length) hreverse
        rw [Word.reverse_length] at hlength
        omega
      have hCeq := C.eq_vertex_of_word_length_eq_zero hCzero
      subst C
      have hsame : i.endpointWord.word =
          (EndpointWord.vertex P S v s).word := by
        rw [hreverse]
        apply Word.ext
        · rfl
        · rfl
        · rfl
      exact detectorLinearMap_bijective_of_word_eq
        f i.endpointWord (EndpointWord.vertex P S v s) hsame (hdetector i)
    · have hlength : 0 < i.endpointWord.word.length := by omega
      have hreverseBijective :=
        detectorLinearMap_reversePairWord_bijective
          f i.endpointWord hlength (hdetector i)
      have hword :
          (detectorEndpoint S (reversePairWord i.endpointWord)).word =
            C.word := by
        rw [EndpointWord.ofWord_word, reversePairWord_eq, hreverse,
          Word.reverse_reverse]
      exact detectorLinearMap_bijective_of_word_eq f
        (detectorEndpoint S (reversePairWord i.endpointWord)) C
        hword hreverseBijective

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
