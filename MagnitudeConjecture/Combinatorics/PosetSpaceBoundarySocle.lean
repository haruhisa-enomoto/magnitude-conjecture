import MagnitudeConjecture.Combinatorics.PosetSpaceBoundaryDiagram

/-!
# The boundary-socle criterion for poset diagrams

For a contravariant diagram on the augmented boundary, the maps from the
non-root values into the root are injective exactly when the diagram has no
nonzero subdiagram supported away from the root.  This is the diagrammatic
content of the manuscript's elementary projective-socle argument: a kernel
at a non-root point generates a submodule invisible at the root, while any
submodule invisible at the root lies in those kernels.

The ring-theoretic identification of root-supported simples with the
projective boundary simple is deliberately kept separate.  The result here
is the intrinsic criterion needed on the incidence-diagram side.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory
open Opposite

universe u

variable (k T : Type u) [Field k] [PartialOrder T]

/-- A pointwise linear subdiagram of a boundary diagram. -/
structure BoundarySubdiagram
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) where
  /-- The chosen subspace at each boundary point. -/
  obj (q : (BoundaryIndex T)ᵒᵖ) : Submodule k (F.obj q)
  /-- Every structure map preserves the chosen subspaces. -/
  map {q r : (BoundaryIndex T)ᵒᵖ} (f : q ⟶ r) :
    obj q ≤ (obj r).comap (F.map f).hom

namespace BoundarySubdiagram

variable {k T}
variable {F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k}

@[ext]
theorem ext {N L : BoundarySubdiagram k T F}
    (h : ∀ q, N.obj q = L.obj q) : N = L := by
  cases N with
  | mk Nobj Nmap =>
      cases L with
      | mk Lobj Lmap =>
          have hobj : Nobj = Lobj := funext h
          subst Lobj
          rfl

/-- A boundary subdiagram is zero when every pointwise subspace is zero. -/
def IsZero (N : BoundarySubdiagram k T F) : Prop :=
  ∀ q, N.obj q = ⊥

/-- A boundary subdiagram is supported away from the root when its root
component vanishes. -/
def SupportedAwayFromRoot (N : BoundarySubdiagram k T F) : Prop :=
  N.obj (op (.root : BoundaryIndex T)) = ⊥

/-- Pointwise containment of boundary subdiagrams. -/
def IsSubdiagramOf (N L : BoundarySubdiagram k T F) : Prop :=
  ∀ q, N.obj q ≤ L.obj q

/-- A nonzero boundary subdiagram is simple when it has no proper nonzero
boundary subdiagram. -/
def IsSimple (N : BoundarySubdiagram k T F) : Prop :=
  ¬ N.IsZero ∧
    ∀ L : BoundarySubdiagram k T F,
      L.IsSubdiagramOf N → ¬ L.IsZero → L = N

/-- A boundary subdiagram meets the root when its root component is
nonzero. -/
def MeetsRoot (N : BoundarySubdiagram k T F) : Prop :=
  N.obj (op (.root : BoundaryIndex T)) ≠ ⊥

theorem isSubdiagramOf_refl (N : BoundarySubdiagram k T F) :
    N.IsSubdiagramOf N :=
  fun _ ↦ le_rfl

theorem IsSubdiagramOf.trans {N L M : BoundarySubdiagram k T F}
    (hNL : N.IsSubdiagramOf L) (hLM : L.IsSubdiagramOf M) :
    N.IsSubdiagramOf M :=
  fun q ↦ (hNL q).trans (hLM q)

theorem IsSubdiagramOf.supportedAwayFromRoot
    {N L : BoundarySubdiagram k T F}
    (hNL : N.IsSubdiagramOf L) (hL : L.SupportedAwayFromRoot) :
    N.SupportedAwayFromRoot := by
  apply le_antisymm
  · exact (hNL _).trans_eq hL
  · exact bot_le

/-- The sum of the dimensions of the pointwise subspaces of a finite
boundary subdiagram. -/
def totalFinrank [Fintype T] (N : BoundarySubdiagram k T F) : ℕ :=
  ∑ q : BoundaryIndex T, Module.finrank k (N.obj (op q))

theorem totalFinrank_mono [Fintype T]
    (hfinite : ∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q)))
    {N L : BoundarySubdiagram k T F} (hNL : N.IsSubdiagramOf L) :
    N.totalFinrank ≤ L.totalFinrank := by
  letI (q : BoundaryIndex T) : Module.Finite k (F.obj (op q)) := hfinite q
  exact Finset.sum_le_sum fun q _ ↦ Submodule.finrank_mono (hNL (op q))

theorem eq_of_isSubdiagramOf_of_totalFinrank_eq [Fintype T]
    (hfinite : ∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q)))
    {N L : BoundarySubdiagram k T F} (hNL : N.IsSubdiagramOf L)
    (hrank : N.totalFinrank = L.totalFinrank) : N = L := by
  letI (q : BoundaryIndex T) : Module.Finite k (F.obj (op q)) := hfinite q
  apply ext
  intro q
  cases q using Opposite.rec with
  | _ q =>
      apply Submodule.eq_of_le_of_finrank_eq (hNL (op q))
      exact (Finset.sum_eq_sum_iff_of_le fun r _ ↦
        Submodule.finrank_mono (hNL (op r))).mp hrank q (Finset.mem_univ q)

/-- Every nonzero subdiagram of a finite-dimensional finite boundary
diagram contains a simple subdiagram. -/
theorem exists_simple_subdiagram [Fintype T]
    (hfinite : ∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q)))
    (N : BoundarySubdiagram k T F) (hN : ¬ N.IsZero) :
    ∃ L : BoundarySubdiagram k T F,
      L.IsSubdiagramOf N ∧ L.IsSimple := by
  classical
  let p : ℕ → Prop := fun d ↦
    ∃ L : BoundarySubdiagram k T F,
      L.IsSubdiagramOf N ∧ ¬ L.IsZero ∧ L.totalFinrank = d
  have hp : ∃ d, p d :=
    ⟨N.totalFinrank, N, isSubdiagramOf_refl N, hN, rfl⟩
  let d := Nat.find hp
  obtain ⟨L, hLN, hL, hLd⟩ := Nat.find_spec hp
  refine ⟨L, hLN, hL, ?_⟩
  intro M hML hM
  have hMN : M.IsSubdiagramOf N := hML.trans hLN
  have hmin : d ≤ M.totalFinrank :=
    Nat.find_min' hp ⟨M, hMN, hM, rfl⟩
  have hle : M.totalFinrank ≤ L.totalFinrank :=
    totalFinrank_mono hfinite hML
  have heq : M.totalFinrank = L.totalFinrank := by
    have hupper : M.totalFinrank ≤ d := hle.trans_eq hLd
    have hMd : M.totalFinrank = d := le_antisymm hupper hmin
    exact hMd.trans hLd.symm
  exact eq_of_isSubdiagramOf_of_totalFinrank_eq hfinite hML heq

/-- The pointwise kernels of all maps to the root form a subdiagram. -/
def rootKernel (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    BoundarySubdiagram k T F where
  obj q := by
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => exact ⊥
        | nonroot t => exact LinearMap.ker (boundaryDiagramRootMap k T F t)
  map := by
    intro q r f
    cases q using Opposite.rec with
    | _ q =>
        cases r using Opposite.rec with
        | _ r =>
            have hrq : r ≤ q := le_of_op_hom f
            cases q with
            | root =>
                cases r with
                | root => exact bot_le
                | nonroot t => exact False.elim hrq
            | nonroot s =>
                cases r with
                | root =>
                    intro x hx
                    change (F.map f).hom x = 0
                    rw [show f = boundaryRootArrow T s from Subsingleton.elim _ _]
                    exact hx
                | nonroot t =>
                    intro x hx
                    change boundaryDiagramRootMap k T F t ((F.map f).hom x) = 0
                    have hst : s ≤ t := hrq
                    rw [show f = boundaryNonrootArrow T hst from
                      Subsingleton.elim _ _]
                    exact (boundaryDiagramRootMap_map_nonroot k T F hst x).trans hx

@[simp]
theorem rootKernel_obj_root
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    (rootKernel (k := k) (T := T) F).obj
      (op (.root : BoundaryIndex T)) = ⊥ :=
  rfl

@[simp]
theorem rootKernel_obj_nonroot
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) (t : T) :
    (rootKernel (k := k) (T := T) F).obj
      (op (.nonroot t : BoundaryIndex T)) =
      LinearMap.ker (boundaryDiagramRootMap k T F t) :=
  rfl

theorem rootKernel_supportedAwayFromRoot
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    (rootKernel (k := k) (T := T) F).SupportedAwayFromRoot :=
  rfl

/-- The root-kernel subdiagram is zero exactly when all maps into the root
are injective. -/
theorem rootKernel_isZero_iff
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    (rootKernel (k := k) (T := T) F).IsZero ↔
      ∀ t : T, Function.Injective (boundaryDiagramRootMap k T F t) := by
  constructor
  · intro h t
    apply LinearMap.ker_eq_bot.mp
    simpa using h (op (.nonroot t : BoundaryIndex T))
  · intro h q
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => rfl
        | nonroot t =>
            exact LinearMap.ker_eq_bot.mpr (h t)

/-- Injectivity of all maps into the root is equivalent to the absence of a
nonzero subdiagram supported away from the root. -/
theorem injective_rootMaps_iff_no_supportedAwaySubdiagram
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    (∀ t : T, Function.Injective (boundaryDiagramRootMap k T F t)) ↔
      ∀ N : BoundarySubdiagram k T F,
        N.SupportedAwayFromRoot → N.IsZero := by
  constructor
  · intro hinjective N hroot q
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => exact hroot
        | nonroot t =>
            apply bot_unique
            intro x hx
            apply hinjective t
            have hmap := N.map (boundaryRootArrow T t) hx
            rw [hroot] at hmap
            change boundaryDiagramRootMap k T F t x = 0 at hmap
            simpa using hmap
  · intro h
    rw [← rootKernel_isZero_iff (k := k) (T := T) F]
    exact h (rootKernel (k := k) (T := T) F)
      (rootKernel_supportedAwayFromRoot (k := k) (T := T) F)

/-- On a finite-dimensional finite boundary diagram, having no nonzero
subdiagram supported away from the root is equivalent to every simple
subdiagram meeting the root.  This is the intrinsic socle formulation of
the root-injectivity criterion. -/
theorem no_supportedAwaySubdiagram_iff_every_simple_meetsRoot [Fintype T]
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k)
    (hfinite : ∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q))) :
    (∀ N : BoundarySubdiagram k T F,
        N.SupportedAwayFromRoot → N.IsZero) ↔
      ∀ L : BoundarySubdiagram k T F, L.IsSimple → L.MeetsRoot := by
  constructor
  · intro h L hsimple hroot
    exact hsimple.1 (h L hroot)
  · intro h N hroot
    by_contra hN
    obtain ⟨L, hLN, hsimple⟩ := exists_simple_subdiagram hfinite N hN
    exact h L hsimple (hLN.supportedAwayFromRoot hroot)

end BoundarySubdiagram

/-- Finite injective boundary diagrams can equivalently be characterized by
finite-dimensional values and the absence of nonzero subdiagrams supported
away from the root. -/
theorem isFiniteInjectiveBoundaryDiagram_iff_no_supportedAwaySubdiagram
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    IsFiniteInjectiveBoundaryDiagram k T F ↔
      (∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q))) ∧
        ∀ N : BoundarySubdiagram k T F,
          N.SupportedAwayFromRoot → N.IsZero := by
  rw [IsFiniteInjectiveBoundaryDiagram]
  refine and_congr_right' ?_
  simpa [boundaryDiagramRootMap] using
    BoundarySubdiagram.injective_rootMaps_iff_no_supportedAwaySubdiagram
      (k := k) (T := T) F

/-- Finite injective boundary diagrams are equivalently the finite diagrams
whose every simple subdiagram meets the root.  Under the incidence-module
interpretation, the root simple is the projective boundary simple, so this
is the manuscript's projective-socle criterion. -/
theorem isFiniteInjectiveBoundaryDiagram_iff_every_simple_meetsRoot
    [Fintype T]
    (F : (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) :
    IsFiniteInjectiveBoundaryDiagram k T F ↔
      (∀ q : BoundaryIndex T, Module.Finite k (F.obj (op q))) ∧
        ∀ L : BoundarySubdiagram k T F,
          L.IsSimple → L.MeetsRoot := by
  rw [isFiniteInjectiveBoundaryDiagram_iff_no_supportedAwaySubdiagram]
  constructor
  · rintro ⟨hfinite, haway⟩
    exact ⟨hfinite,
      (BoundarySubdiagram.no_supportedAwaySubdiagram_iff_every_simple_meetsRoot
        F hfinite).mp haway⟩
  · rintro ⟨hfinite, hsimple⟩
    exact ⟨hfinite,
      (BoundarySubdiagram.no_supportedAwaySubdiagram_iff_every_simple_meetsRoot
        F hfinite).mpr hsimple⟩

end MagnitudeConjecture.PosetSpace
