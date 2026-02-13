import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P3_of_P2 {X} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  exact hP2.trans hmono

theorem P1_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have h_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure h_int

theorem P2_univ {X} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simp [interior_univ, closure_univ] at *

theorem P3_iff_forall_point {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3 x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    exact ⟨interior (closure A), isOpen_interior, hx_int, interior_subset⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    have h_closure_nhds : (closure A : Set X) ∈ 𝓝 x := by
      have hU_nhds : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
      exact Filter.mem_of_superset hU_nhds hUsubset
    exact (mem_interior_iff_mem_nhds).2 h_closure_nhds

theorem P2_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- Since `A` is open, it is contained in the interior of its closure.
  have hx_int_closure : x ∈ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact h_subset hx
  -- Rewrite `interior (closure (interior A))` using `hA.interior_eq`.
  simpa [hA.interior_eq] using hx_int_closure

theorem P1_of_P2 {X} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P3_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  intro x hxA
  -- First, show that `closure A` is the whole space.
  have hclosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · have : (Set.univ : Set X) ⊆ closure A := by
        simpa [h] using (closure_mono (interior_subset : interior A ⊆ A))
      exact this
  -- Hence its interior is also the whole space.
  have hinterior : interior (closure A) = (Set.univ : Set X) := by
    simpa [hclosureA, interior_univ]
  -- Conclude the desired membership.
  simpa [hinterior] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_union {X} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure A) := hA hxA
      have hmono : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hmono hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure B) := hB hxB
      have hmono : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hmono hx_int

theorem P3_iff_forall_closed_nbhd {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∃ C, IsClosed C ∧ x ∈ interior C ∧ C ⊆ closure A := by
  -- First, recall the characterization of `P3 A` in terms of open neighbourhoods.
  have h_open : P3 A ↔ ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A :=
    P3_iff_forall_point
  -- We now build the desired equivalence.
  constructor
  · intro hP3
    -- Use the open–neighbourhood formulation.
    have h := (h_open).1 hP3
    intro x hxA
    rcases h x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    -- Let `C = closure U`.
    refine ⟨closure U, isClosed_closure, ?_, ?_⟩
    · -- `x ∈ interior C`.
      have hU_in_int : (U : Set X) ⊆ interior (closure U) :=
        interior_maximal subset_closure hUopen
      exact hU_in_int hxU
    · -- `C ⊆ closure A`.
      have hCsubset : closure U ⊆ closure A := by
        have h' : closure U ⊆ closure (closure A) := closure_mono hUsubset
        simpa [closure_closure] using h'
      exact hCsubset
  · intro hClosed
    -- Build the open–neighbourhood formulation from the closed one.
    have h : ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
      intro x hxA
      rcases hClosed x hxA with ⟨C, hCclosed, hxintC, hCsubset⟩
      refine ⟨interior C, isOpen_interior, hxintC, ?_⟩
      exact interior_subset.trans hCsubset
    exact (h_open).2 h

theorem P2_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) : P2 A := by
  intro x hxA
  have hinterior : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hinterior] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P1_union {X} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` originates from `A`
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in the desired closure
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsubset_int : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset_int
      exact hsubset hx_closureA
  | inr hxB =>
      -- `x` originates from `B`
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in the desired closure
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsubset_int : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset_int
      exact hsubset hx_closureB

theorem P3_empty {X} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_iff_P3_of_closed {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro hP3
    -- First, show that `A ⊆ interior A`, hence `interior A = A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    have h_eq : (interior A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset
    -- Therefore `A` is open.
    have hAopen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_eq] using this
    -- Apply the open–set version of `P2`.
    exact P2_of_open hAopen

theorem P1_iff_P2_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_of_open hA
  · intro hP2
    exact P1_of_P2 hP2

theorem P2_union {X} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      -- Monotonicity chain: `interior A ⊆ interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have hsubset_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Finally, take interiors again
      have hsubset :
          interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      -- Monotonicity chain: `interior B ⊆ interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Hence `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hsubset_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Take interiors again
      have hsubset :
          interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_int

theorem P1_empty {X} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty {X} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_univ {X} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simp [interior_univ, closure_univ] at hx
  simpa using hx

theorem P1_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) : P1 A := by
  intro x hxA
  simpa [h] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  simpa using (P3_of_P2 (P2_of_open hA))

theorem P3_of_dense {X} [TopologicalSpace X] {A : Set X} (h : closure A = (Set.univ : Set X)) : P3 A := by
  intro x hxA
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [h, interior_univ]
  simpa [hInt]

theorem P3_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P3 A) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP3A : P3 A := hAll A hAℱ
  have hx_intA : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hsubset_closure : closure A ⊆ closure (⋃₀ ℱ) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ ℱ := Set.subset_sUnion_of_mem hAℱ
      exact closure_mono hA_subset
    exact interior_mono hsubset_closure
  exact hsubset hx_intA

theorem P2_bUnion {X I} [TopologicalSpace X] {F : I → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  -- Apply `P2` for the chosen index `i`.
  have hx_int : x ∈ interior (closure (interior (F i))) := (hAll i) hxFi
  -- Establish the inclusion chains needed for monotonicity.
  have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
    interior_mono (Set.subset_iUnion _ _)
  have hsubset_closure :
      closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
    closure_mono hsubset_int
  have hsubset :
      interior (closure (interior (F i))) ⊆
      interior (closure (interior (⋃ j, F j))) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P2_iff_P1_of_closure_open {X} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hxA
    -- `closure A ⊆ closure (interior A)`
    have h_closure_subset : (closure (A) : Set X) ⊆ closure (interior A) := by
      simpa [closure_closure] using
        (closure_mono (hP1 : (A : Set X) ⊆ closure (interior A)))
    -- Since `closure A` is open, it is contained in the interior of `closure (interior A)`
    have h_closure_subset_int :
        (closure (A) : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal h_closure_subset h
    -- `x` belongs to `closure A`, hence to the desired interior
    have hx_closure : x ∈ closure A := subset_closure hxA
    exact h_closure_subset_int hx_closure

theorem P3_of_closure_open {X} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [h.interior_eq] using hx_closure

theorem P3_of_interior_eq {X} [TopologicalSpace X] {A : Set X} (h : interior A = A) : P3 A := by
  intro x hxA
  -- turn the hypothesis into a membership of `interior A`
  have hx_int : x ∈ interior A := by
    simpa [h] using hxA
  -- `interior A` is contained in `interior (closure A)`
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int

theorem P1_of_closure_eq {X} [TopologicalSpace X] {A : Set X} (h : closure A = closure (interior A)) : P1 A := by
  intro x hx
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hx
  simpa [h] using hx_closure

theorem P2_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P2 A) : P2 (⋃₀ ℱ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP2A : P2 A := h A hAℱ
  have hx_intA : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ ℱ) :=
    interior_mono (Set.subset_sUnion_of_mem hAℱ)
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
    closure_mono hsubset_int
  have hsubset :
      interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ ℱ))) :=
    interior_mono hsubset_closure
  exact hsubset hx_intA

theorem P1_iUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_cl : x ∈ closure (interior (F i)) := (h i) hxFi
  have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
    interior_mono (Set.subset_iUnion _ _)
  have hsubset_cl : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
    closure_mono hsubset_int
  exact hsubset_cl hx_cl

theorem P1_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P1 A) : P1 (⋃₀ ℱ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP1A : P1 A := h A hAℱ
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ ℱ) :=
    interior_mono (Set.subset_sUnion_of_mem hAℱ)
  have hsubset_cl : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
    closure_mono hsubset_int
  exact hsubset_cl hx_cl

theorem P1_iff_closure_interior {X} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro hP1
    -- We always have `closure (interior A) ⊆ closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- From `A ⊆ closure (interior A)`, taking closures yields the reverse inclusion.
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact Set.Subset.antisymm h₁ h₂
  · intro hEq
    -- Since `A ⊆ closure A` and the closures are equal, the desired inclusion holds.
    have : A ⊆ closure A := subset_closure
    simpa [hEq] using this

theorem P2_iUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P2 (F i)) : P2 (⋃ i, F i) := by
  simpa using P2_bUnion (F := F) h

theorem P1_closed_of_P3 {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P1 A := by
  intro hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed hA).mpr hP3
  exact P1_of_P2 hP2

theorem exists_P3_subset {X} [TopologicalSpace X] {A : Set X} : ∃ B, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  exact P3_empty

theorem P3_iff_nhds {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, (closure A : Set X) ∈ 𝓝 x := by
  unfold P3
  constructor
  · intro hP3 x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h x hxA
    have h_nhds : (closure A : Set X) ∈ 𝓝 x := h x hxA
    exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P2_interior {X} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P2 (interior A) := by
  intro x hx
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hx
  -- Apply `P2 A` to get the desired membership.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Simplify the goal using `interior_interior`.
  simpa [interior_interior] using hx_int

theorem P3_interior {X} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P3 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  exact hsubset hx

theorem P1_closure {X} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- First inclusion: `closure A ⊆ closure (interior A)`
  have h1 : (closure (A : Set X)) ⊆ closure (interior A) := by
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono h
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h
  -- Combine the inclusions
  have hsubset : (closure (A : Set X)) ⊆ closure (interior (closure A)) :=
    h1.trans h2
  exact hsubset hx

theorem P2_interior_uncond {X} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure, hence in the interior of that closure.
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  -- Apply the inclusion and simplify.
  simpa [interior_interior] using hsubset hx

theorem P3_singleton_of_dense {X} [TopologicalSpace X] {x : X} : Dense ({x} : Set X) → P3 ({x} : Set X) := by
  intro hDense
  have hclosure : closure ({x} : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  exact P3_of_dense (A := ({x} : Set X)) hclosure

theorem P2_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  -- Split the hypothesis on the product set.
  rcases hp with ⟨hAp, hBp⟩
  -- Auxiliary open neighbourhoods coming from the `P2` hypotheses.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hxU : p.1 ∈ U := by
    dsimp [U] at *
    exact hA hAp
  have hyV : p.2 ∈ V := by
    dsimp [V] at *
    exact hB hBp
  have h_mem : p ∈ U ×ˢ V := by
    exact ⟨hxU, hyV⟩
  -- `U ×ˢ V` is open.
  have h_open : IsOpen (U ×ˢ V) := by
    have hUopen : IsOpen U := by
      dsimp [U]; exact isOpen_interior
    have hVopen : IsOpen V := by
      dsimp [V]; exact isOpen_interior
    exact hUopen.prod hVopen
  ----------------------------------------------------------------
  -- 1.  `U ×ˢ V ⊆ closure (interior A) ×ˢ closure (interior B)`.
  ----------------------------------------------------------------
  have h_sub₁ :
      (U ×ˢ V) ⊆ closure (interior A) ×ˢ closure (interior B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    dsimp [U, V] at hq1 hq2
    exact ⟨interior_subset hq1, interior_subset hq2⟩
  ----------------------------------------------------------------
  -- 2.  `closure (interior A) ×ˢ closure (interior B)`
  --     ⊆ `closure (interior (A ×ˢ B))`.
  ----------------------------------------------------------------
  -- First, `interior A × interior B` is an open subset of `A × B`,
  -- hence it lies in the interior of `A × B`.
  have h_int_prod_subset :
      interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
    have h_into : interior A ×ˢ interior B ⊆ A ×ˢ B := by
      intro q hq; exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open_int : IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior).prod isOpen_interior
    exact interior_maximal h_into h_open_int
  -- Taking closures gives the next inclusion.
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_prod_subset
  -- Identify the left–hand side using `closure_prod_eq`.
  have h_prod_closure_eq :
      closure (interior A ×ˢ interior B) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using
      (closure_prod_eq (s := interior A) (t := interior B))
  have h_sub₂ :
      closure (interior A) ×ˢ closure (interior B) ⊆
        closure (interior (A ×ˢ B)) := by
    simpa [h_prod_closure_eq] using h_closure_subset
  ----------------------------------------------------------------
  -- 3.  Combine the two inclusions.
  ----------------------------------------------------------------
  have h_sub_total :
      (U ×ˢ V) ⊆ closure (interior (A ×ˢ B)) :=
    Set.Subset.trans h_sub₁ h_sub₂
  ----------------------------------------------------------------
  -- 4.  Pass to the interior of the target set.
  ----------------------------------------------------------------
  have h_sub_int :
      (U ×ˢ V) ⊆ interior (closure (interior (A ×ˢ B))) :=
    interior_maximal h_sub_total h_open
  ----------------------------------------------------------------
  -- 5.  Conclude the desired membership.
  ----------------------------------------------------------------
  exact h_sub_int h_mem

theorem P3_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Open neighbourhood for the first component
  obtain ⟨U, hUopen, hp1U, hUsubset⟩ :=
    (P3_iff_forall_point).1 hA _ hpA
  -- Open neighbourhood for the second component
  obtain ⟨V, hVopen, hp2V, hVsubset⟩ :=
    (P3_iff_forall_point).1 hB _ hpB
  -- The product of the two neighbourhoods is open
  have h_open : IsOpen (U ×ˢ V) := hUopen.prod hVopen
  -- The point `p` lies in this product neighbourhood
  have hp_in : p ∈ U ×ˢ V := by
    exact ⟨hp1U, hp2V⟩
  -- The product neighbourhood is contained in the closure of `A ×ˢ B`
  have hsubset_closure : (U ×ˢ V) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    have hmem : q ∈ closure A ×ˢ closure B := ⟨hUsubset hqU, hVsubset hqV⟩
    simpa [closure_prod_eq] using hmem
  -- Hence it is contained in the interior of that closure
  have hsubset_int :
      (U ×ˢ V) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hsubset_closure h_open
  -- Conclude the desired membership
  exact hsubset_int hp_in

theorem P2_to_P3_interior {X} [TopologicalSpace X] {A : Set X} : P2 A → P3 (interior A) := by
  intro _hP2
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact hsubset hx

theorem exists_dense_P2_subset {X} [TopologicalSpace X] {A : Set X} : Dense A → ∃ B, B ⊆ A ∧ P2 B := by
  intro _
  exact ⟨interior A, interior_subset, P2_interior_uncond (A := A)⟩

theorem P3_bUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P3 (F i)) : P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (F i)) := (h i) hxFi
  have hsubset_closure : closure (F i) ⊆ closure (⋃ j, F j) := by
    have : (F i : Set X) ⊆ ⋃ j, F j := Set.subset_iUnion _ _
    exact closure_mono this
  have hsubset_int :
      interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) :=
    interior_mono hsubset_closure
  exact hsubset_int hx_intFi

theorem exists_maximal_P3_subset {X} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P3 B ∧ ∀ C, C ⊆ A → P3 C → C ⊆ B := by
  classical
  -- Define the family of all `P3`-subsets of `A`.
  let ℱ : Set (Set X) := {C | C ⊆ A ∧ P3 C}
  -- Take their union as the candidate maximal set.
  refine ⟨⋃₀ ℱ, ?_, ?_, ?_⟩
  -- 1.  `⋃₀ ℱ ⊆ A`.
  · intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCℱ, hxC⟩
    exact (hCℱ.1) hxC
  -- 2.  `P3 (⋃₀ ℱ)`.
  ·
    have h_all : ∀ C, C ∈ ℱ → P3 C := by
      intro C hC
      exact hC.2
    exact P3_sUnion (ℱ := ℱ) h_all
  -- 3.  Maximality: every `P3` subset of `A` is contained in `⋃₀ ℱ`.
  · intro C hCsub hP3C
    have hCmem : C ∈ ℱ := ⟨hCsub, hP3C⟩
    intro x hx
    exact Set.mem_sUnion.2 ⟨C, hCmem, hx⟩

theorem P1_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Membership in the relevant closures for each component
  have h1 : p.1 ∈ closure (interior A) := hA hpA
  have h2 : p.2 ∈ closure (interior B) := hB hpB
  have h_mem : p ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨h1, h2⟩
  ----------------------------------------------------------------
  -- Show that the product of these closures is contained in the
  -- target closure.
  ----------------------------------------------------------------
  -- Step 1: `interior A × interior B ⊆ interior (A × B)`
  have h_int_prod_subset :
      interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
    have h_sub : interior A ×ˢ interior B ⊆ A ×ˢ B := by
      intro q hq
      exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open : IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior).prod isOpen_interior
    exact interior_maximal h_sub h_open
  -- Step 2: take closures
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_prod_subset
  -- Step 3: identify the left-hand closure via `closure_prod_eq`
  have h_prod_closure_eq :
      closure (interior A ×ˢ interior B) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using closure_prod_eq (s := interior A) (t := interior B)
  -- Step 4: collect the inclusions
  have h_sub :
      closure (interior A) ×ˢ closure (interior B) ⊆
        closure (interior (A ×ˢ B)) := by
    simpa [h_prod_closure_eq] using h_closure_subset
  ----------------------------------------------------------------
  -- Final step: apply the inclusion to the point `p`.
  ----------------------------------------------------------------
  exact h_sub h_mem

theorem P2_iff_P3_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _hP3
    exact P2_of_open hA

theorem exists_maximal_P1_subset {X} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B ∧ (∀ C, C ⊆ A → P1 C → C ⊆ B) := by
  classical
  -- Define the family of all `P1` subsets of `A`.
  let ℱ : Set (Set X) := {C | C ⊆ A ∧ P1 C}
  refine ⟨⋃₀ ℱ, ?_, ?_, ?_⟩
  · -- `⋃₀ ℱ ⊆ A`
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCℱ, hxC⟩
    exact (hCℱ.1) hxC
  · -- `P1 (⋃₀ ℱ)`
    have hP1 : P1 (⋃₀ ℱ) := by
      have hAll : ∀ C, C ∈ ℱ → P1 C := by
        intro C hC
        exact hC.2
      exact P1_sUnion (ℱ := ℱ) hAll
    exact hP1
  · -- Maximality
    intro C hCsub hP1C
    have hCmem : C ∈ ℱ := ⟨hCsub, hP1C⟩
    intro x hx
    exact Set.mem_sUnion.2 ⟨C, hCmem, hx⟩

theorem P3_of_dense_subset {X} [TopologicalSpace X] {A B : Set X} (hsub : B ⊆ A) (hDense : Dense B) : P3 A := by
  -- `closure B` is the whole space since `B` is dense.
  have hB : closure (B : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- From `B ⊆ A`, we obtain `closure B ⊆ closure A`.
  have hsubset : (closure (B : Set X)) ⊆ closure (A : Set X) := closure_mono hsub
  -- Hence `closure A` is also the whole space.
  have hA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    simpa [hB] using hsubset
  -- Apply the existing lemma `P3_of_dense`.
  exact P3_of_dense (A := A) hA

theorem P2_singleton_of_discrete {X} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P2 ({x} : Set X) := by
  -- `{x}` is open in a discrete topology.
  have h_open : IsOpen ({x} : Set X) := by
    simpa using isOpen_discrete (s := ({x} : Set X))
  -- Apply the lemma for open sets.
  exact P2_of_open (A := {x}) h_open

theorem P2_subsingleton {X} [TopologicalSpace X] {A : Set X} [Subsingleton X] : P2 A := by
  intro x hxA
  -- In a subsingleton, any non-empty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro y hy
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hxA
  -- Rewriting shows the desired interior is the whole space.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_subsingleton {X} [TopologicalSpace X] {A : Set X} [Subsingleton X] : P3 A := by
  simpa using (P3_of_P2 (A := A) P2_subsingleton)

theorem P1_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P1 A := by
  intro x hx
  have hclosure : (closure (interior A) : Set X) = Set.univ := by
    simpa [h, closure_univ]
  simpa [hclosure] using (Set.mem_univ x)

theorem P2_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P2 A := by
  intro x hxA
  have h_closure : (closure (interior A) : Set X) = Set.univ := by
    simpa [h, closure_univ]
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  simpa [h_int]

theorem P3_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := by
    simpa [h, closure_univ]
  exact P3_of_dense_interior (A := A) hclosure

theorem P1_interior {X} [TopologicalSpace X] {A : Set X} : P1 A → P1 (interior A) := by
  intro hP1
  intro x hx
  have : x ∈ closure (interior A) := hP1 (interior_subset hx)
  simpa [interior_interior] using this

theorem P1_interior_closure {X} [TopologicalSpace X] {A : Set X} : P1 (interior (closure A)) := by
  intro x hx
  have hx_cl : x ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using hx_cl

theorem exists_P2_superset {X} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, ?_⟩
  simpa using (P2_univ (X := X))

theorem exists_compact_P2_subset {X} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, ?_⟩
  exact P2_empty (X := X)

theorem P1_interior_of_P3 {X} [TopologicalSpace X] {A : Set X} : P3 A → P1 (interior A) := by
  intro _hP3
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P1_iUnion_interior {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, interior (F i)) := by
  intro x hx
  -- The union of interiors is open, hence its interior is itself.
  have h_open : IsOpen (⋃ i, interior (F i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  have h_int_eq : interior (⋃ i, interior (F i)) = ⋃ i, interior (F i) :=
    h_open.interior_eq
  -- From `x ∈ ⋃ i, interior (F i)` we get `x ∈ closure (⋃ i, interior (F i))`.
  have hx_cl : x ∈ closure (⋃ i, interior (F i)) := subset_closure hx
  -- Rewrite the target using `h_int_eq`.
  simpa [h_int_eq] using hx_cl

theorem P2_iff_P1_of_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense A) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hxA
    -- First, prove that `closure (interior A)` is the whole space.
    have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · -- Since `A ⊆ closure (interior A)` (from `P1`) and `A` is dense,
        -- we get `closure A = univ ⊆ closure (interior A)`.
        have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
          have hA_subset : (A : Set X) ⊆ closure (interior A) := hP1
          simpa [closure_closure] using closure_mono hA_subset
        simpa [h.closure_eq] using h_subset
    -- Hence the interior of this closure is also the whole space.
    have h_int_univ : interior (closure (interior A)) = (Set.univ : Set X) := by
      simpa [h_closure_int, interior_univ]
    -- Conclude the desired membership.
    have : x ∈ (Set.univ : Set X) := by
      exact Set.mem_univ x
    simpa [h_int_univ] using this

theorem exists_open_P2_superset {X} [TopologicalSpace X] {A : Set X} (h : P2 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ _, ?_⟩
  simpa using P2_univ (X := X)

theorem P2_nhds {X} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, interior (closure (interior A)) ∈ 𝓝 x := by
  unfold P2
  constructor
  · intro hP2 x hxA
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
    exact (isOpen_interior.mem_nhds hx_int)
  · intro h x hxA
    have h_nhds : interior (closure (interior A)) ∈ 𝓝 x := h x hxA
    exact mem_of_mem_nhds h_nhds

theorem P1_interior_eq_closure {X} [TopologicalSpace X] {A : Set X} : interior A = closure A → P1 A := by
  intro hEq
  intro x hxA
  have hx_cl : x ∈ (closure A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior A := by
    simpa [hEq.symm] using hx_cl
  exact subset_closure hx_int

theorem P2_basis {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U ∈ 𝓝 x, U ⊆ A) → P2 A := by
  intro hBasis
  intro x hxA
  -- Obtain a neighbourhood of `x` contained in `A`.
  rcases hBasis x hxA with ⟨U, hU_nhds, hU_sub⟩
  -- Therefore `A` itself is a neighbourhood of `x`.
  have hA_nhds : (A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset hU_nhds hU_sub
  -- Hence `x` lies in the interior of `A`.
  have hx_intA : x ∈ interior A :=
    (mem_interior_iff_mem_nhds).2 hA_nhds
  -- `interior A` is open and contained in `closure (interior A)`,
  -- so it is contained in the interior of that closure.
  have hsubset :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact hsubset hx_intA

theorem P1_basis {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ A) → P1 A := by
  intro hBasis
  intro x hxA
  rcases hBasis x hxA with ⟨U, hUopen, hxU, hUsub⟩
  have hA_nhds : (A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset (hUopen.mem_nhds hxU) hUsub
  have hx_int : x ∈ interior A := (mem_interior_iff_mem_nhds).2 hA_nhds
  exact subset_closure hx_int

theorem P1_subsingleton {X} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  simpa using (P1_of_P2 (A := A) P2_subsingleton)

theorem P2_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P2_prod (A := A) (B := (Set.univ : Set Y)) hA (by
      simpa using (P2_univ (X := Y))))

theorem P1_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hA (by
      simpa using (P1_univ (X := Y))))

theorem P3_prod_univ {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : P3 (Set.univ : Set Y) := by
    simpa using (P3_of_open (A := (Set.univ : Set Y)) isOpen_univ)
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P2_iff_P3_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A ↔ P3 A := by
  -- From density we know the closure of `interior A` is the whole space.
  have hClosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _hP3
    exact P2_of_dense_interior (A := A) hClosure

theorem P3_interior_closure {X} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  simpa using (P3_of_open (A := interior (closure A)) isOpen_interior)

theorem P1_iff_P2_of_boundary_empty {X} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P1 A ↔ P2 A := by
  -- First, prove `closure A ⊆ interior A` from `frontier A = ∅`.
  have h_subset : (closure (A : Set X)) ⊆ interior A := by
    intro x hx_cl
    by_cases hx_int : x ∈ interior A
    · exact hx_int
    · -- Otherwise `x` would lie in the (empty) frontier – contradiction.
      have hx_frontier : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        exact And.intro hx_cl hx_int
      have h_not_mem : x ∉ frontier A := by
        -- No point lies in an empty set.
        have h_forall := (Set.eq_empty_iff_forall_not_mem).1 h
        exact h_forall x
      exact False.elim (h_not_mem hx_frontier)
  ----------------------------------------------------------------
  -- From the two inclusions we deduce `interior A = A`, hence `A` is open.
  ----------------------------------------------------------------
  have h_int_eq : (interior A : Set X) = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have : x ∈ closure (A : Set X) := subset_closure hxA
      exact h_subset this
  have hA_open : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [h_int_eq] using this
  ----------------------------------------------------------------
  -- For open sets `P1` and `P2` coincide.
  ----------------------------------------------------------------
  simpa using (P1_iff_P2_of_open (A := A) hA_open)

theorem exists_dense_P3_superset {X} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ Dense B ∧ P3 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, dense_univ, ?_⟩
  simpa using (P3_of_open (A := (Set.univ : Set X)) isOpen_univ)

theorem P1_iff_P3_of_clopen {X} [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) : P1 A ↔ P3 A := by
  simpa using
    ((P1_iff_P2_of_open (A := A) hOpen).trans
      (P2_iff_P3_of_closed (A := A) hClosed))

theorem P1_of_nowhereDense {X} [TopologicalSpace X] {A : Set X} (hN : IsNowhereDense A) : P1 A → A = ∅ := by
  intro hP1
  -- From `IsNowhereDense`, the interior of the closure of `A` is empty.
  have hIntClosure : interior (closure (A : Set X)) = (∅ : Set X) := by
    simpa [IsNowhereDense] using hN
  -- Hence the interior of `A` itself is empty.
  have hIntA : (interior A : Set X) = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have : x ∈ interior (closure A) := by
        have hsubset : (interior A : Set X) ⊆ interior (closure A) :=
          interior_mono (subset_closure : (A : Set X) ⊆ closure A)
        exact hsubset hx
      simpa [hIntClosure] using this
    · exact Set.empty_subset _
  -- Consequently, the closure of the interior of `A` is empty.
  have hClosureInt : closure (interior A) = (∅ : Set X) := by
    simpa [hIntA, closure_empty]
  -- Using `P1`, every point of `A` lies in this empty set, hence `A` is empty.
  have hA_subset_empty : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior A) := hP1 hxA
    simpa [hClosureInt] using this
  exact Set.Subset.antisymm hA_subset_empty (Set.empty_subset _)

theorem P3_Union_closure {X} [TopologicalSpace X] {I : Type*} {F : I → Set X} (h : ∀ i, P3 (closure (F i))) : P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hP3_cl : P3 (closure (F i)) := h i
  have hx_int : x ∈ interior (closure (F i)) := by
    have h' := hP3_cl (subset_closure hxFi)
    simpa [closure_closure] using h'
  have hsubset :
      (interior (closure (F i)) : Set X) ⊆ interior (closure (⋃ i, F i)) := by
    have hcl_subset : (closure (F i) : Set X) ⊆ closure (⋃ i, F i) := by
      have : (F i : Set X) ⊆ ⋃ i, F i := Set.subset_iUnion _ _
      exact closure_mono this
    exact interior_mono hcl_subset
  exact hsubset hx_int

theorem P3_of_separated {X} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ Aᶜ ⊆ V ∧ Disjoint U V) : P3 A := by
  -- Use the open–neighbourhood characterisation of `P3`.
  refine (P3_iff_forall_point).2 ?_
  intro x hxA
  -- Obtain separating open sets for the point `x`.
  rcases h x hxA with
    ⟨U, V, hUopen, _hVopen, hxU, hAc_sub_V, hDisj⟩
  -- Show that `U ⊆ closure A`.
  have hU_subset_closure : (U : Set X) ⊆ closure (A : Set X) := by
    intro y hyU
    -- First, prove that `y ∈ A`.
    have h_yA : y ∈ (A : Set X) := by
      classical
      by_cases hA : y ∈ A
      · exact hA
      · -- Otherwise, `y ∈ Aᶜ ⊆ V`, contradicting the disjointness of `U` and `V`.
        have hyV : y ∈ V := hAc_sub_V (by
          simpa using hA)
        have hFalse : False := (Set.disjoint_left.1 hDisj) hyU hyV
        exact (False.elim hFalse)
    -- Hence `y` lies in `closure A`.
    exact subset_closure h_yA
  -- Supply the required neighbourhood data for `P3`.
  exact ⟨U, hUopen, hxU, hU_subset_closure⟩

theorem P2_closed_iff_open_compl {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    -- First, we show `A ⊆ interior A`.
    have h_subset_cl : (closure (interior A) : Set X) ⊆ A := by
      have h' : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using h'
    have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
      interior_mono h_subset_cl
    have hA_subset_int : (A : Set X) ⊆ interior A := by
      intro x hxA
      have hx_int_cl : x ∈ interior (closure (interior A)) := hP2 hxA
      exact h_int_subset hx_int_cl
    -- Hence `interior A = A`, so `A` is open.
    have h_eq : (interior A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hA_subset_int
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hOpen
    exact P2_of_open (A := A) hOpen

theorem P1_prod_closure {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (closure A ×ˢ closure B) := by
  intro hA hB
  -- Upgrade the hypotheses to the closures of `A` and `B`.
  have hA_closure : P1 (closure A) := (P1_closure (A := A)) hA
  have hB_closure : P1 (closure B) := (P1_closure (X := Y) (A := B)) hB
  -- Apply the product lemma.
  simpa using
    (P1_prod (A := closure A) (B := closure B) hA_closure hB_closure)

theorem P3_sUnion_closure {X} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A ∈ ℱ, P3 (closure A)) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP3_cl : P3 (closure A) := hAll A hAℱ
  have hx_int : x ∈ interior (closure A) := by
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [closure_closure] using hP3_cl hx_cl
  have hsubset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hcl_subset : (closure A : Set X) ⊆ closure (⋃₀ ℱ) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ ℱ := Set.subset_sUnion_of_mem hAℱ
      exact closure_mono hA_subset
    exact interior_mono hcl_subset
  exact hsubset hx_int

theorem P3_of_interior_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P3 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  exact P3_of_dense_interior (A := A) hclosure

theorem P2_of_interior_dense {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  exact P2_of_dense_interior (A := A) hclosure

theorem P2_iff_exists_open_nbhd {X} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure (interior A)) := by
  unfold P2
  constructor
  · intro hP2 x hxA
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    exact ⟨interior (closure (interior A)), isOpen_interior, hx, subset_rfl⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, _hUopen, hxU, hUsubset⟩
    exact hUsubset hxU

theorem P1_iterate {X} [TopologicalSpace X] {A : Set X} : P1 (closure (interior (closure (interior A)))) := by
  -- Unfold the definition of `P1`.
  intro x hx
  ----------------------------------------------------------------
  -- 1.  `interior (closure (interior A))` is open and contained in its
  --     own closure, hence it lies in the interior of that closure.
  ----------------------------------------------------------------
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (closure (interior A)))) := by
    -- `interior (closure (interior A))` is open.
    have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
    -- It is, of course, contained in its closure.
    have h_le :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior A))) :=
      subset_closure
    -- Therefore it is contained in the interior of that closure.
    exact interior_maximal h_le h_open
  ----------------------------------------------------------------
  -- 2.  Taking closures yields the inclusion we need for `P1`.
  ----------------------------------------------------------------
  have h_closure :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure (interior (closure (interior A))))) :=
    closure_mono h_subset
  ----------------------------------------------------------------
  -- 3.  Apply the inclusion to the given point `x`.
  ----------------------------------------------------------------
  exact h_closure hx

theorem P2_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (e '' A) := by
  classical
  ----------------------------------------------------------------
  -- A fundamental equality: the homeomorphism transports the `P2`
  -- neighbourhood in the expected way.
  ----------------------------------------------------------------
  have hImageEq :
      (e '' interior (closure (interior A)) : Set Y) =
        interior (closure (interior (e '' A))) := by
    calc
      e '' interior (closure (interior A))
          = interior (e '' closure (interior A)) := by
              simpa using e.image_interior (s := closure (interior A))
      _   = interior (closure (e '' interior A)) := by
              simpa [e.image_closure (s := interior A)]
      _   = interior (closure (interior (e '' A))) := by
              simpa [e.image_interior (s := A)]
  ----------------------------------------------------------------
  -- Forward direction: `P2 A → P2 (e '' A)`.
  ----------------------------------------------------------------
  have forward : P2 A → P2 (e '' A) := by
    intro hP2
    intro y hy
    -- pick a preimage point
    rcases hy with ⟨x, hxA, rfl⟩
    -- apply `P2` for `A`
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    -- transport through `e`
    have h_mem : e x ∈ e '' interior (closure (interior A)) := ⟨x, hx, rfl⟩
    -- rewrite via the equality `hImageEq`
    simpa [hImageEq] using h_mem
  ----------------------------------------------------------------
  -- Backward direction: `P2 (e '' A) → P2 A`.
  ----------------------------------------------------------------
  have backward : P2 (e '' A) → P2 A := by
    intro hP2img
    intro x hxA
    -- apply `P2` for the image set
    have hy : e x ∈ interior (closure (interior (e '' A))) :=
      hP2img ⟨x, hxA, rfl⟩
    -- rewrite via `hImageEq`
    have hy' : e x ∈ e '' interior (closure (interior A)) := by
      simpa [hImageEq] using hy
    -- unpack the image–membership and use injectivity
    rcases hy' with ⟨x', hx'int, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'int
  ----------------------------------------------------------------
  -- Assemble the equivalence.
  ----------------------------------------------------------------
  exact ⟨forward, backward⟩

theorem P2_induction {X} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ B, IsClosed B ∧ x ∈ B ∧ B ⊆ A ∧ P2 B) : P2 A := by
  classical
  -- Define the family of all closed `P2`-subsets of `A`.
  let ℱ : Set (Set X) := {B | IsClosed B ∧ B ⊆ A ∧ P2 B}
  -- Every member of `ℱ` satisfies `P2`.
  have hP2_ℱ : ∀ B, B ∈ ℱ → P2 B := by
    intro B hB
    exact hB.2.2
  -- `P2` holds for the union of all sets in `ℱ`.
  have hP2_union : P2 (⋃₀ ℱ) :=
    P2_sUnion (ℱ := ℱ) hP2_ℱ
  -- The union of all sets in `ℱ` is exactly `A`.
  have h_union_eq : (⋃₀ ℱ : Set X) = A := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_sUnion.1 hx with ⟨B, hBℱ, hxB⟩
      exact (hBℱ.2.1) hxB
    · intro x hxA
      rcases h x hxA with ⟨B, hBclosed, hxB, hBsub, hBP2⟩
      have hBmem : B ∈ ℱ := by
        exact ⟨hBclosed, hBsub, hBP2⟩
      exact Set.mem_sUnion.2 ⟨B, hBmem, hxB⟩
  -- Transport `P2` through the equality.
  simpa [h_union_eq] using hP2_union

theorem P2_setdiff {X} [TopologicalSpace X] {A B : Set X} : P2 A → IsClosed B → B ⊆ A → P2 (A \ B) := by
  classical
  intro hP2 hBclosed hBsub
  -- We unfold the definition of `P2 (A \ B)`.
  intro x hxDiff
  rcases hxDiff with ⟨hxA, hxNotB⟩
  -- Step 1: `P2 A` gives us a good open neighbourhood of `x`.
  have hxK : x ∈ interior (closure (interior A)) := hP2 hxA
  have hKopen : IsOpen (interior (closure (interior A))) := isOpen_interior
  -- Step 2: work in the open set `O := K ∩ Bᶜ`.
  let O : Set X := interior (closure (interior A)) ∩ (Bᶜ : Set X)
  have hOopen : IsOpen O :=
    hKopen.inter hBclosed.isOpen_compl
  have hxO : x ∈ O := by
    dsimp [O]
    exact And.intro hxK hxNotB
  ------------------------------------------------------------------
  -- Goal:  `O ⊆ closure (interior (A \ B))`.
  ------------------------------------------------------------------
  have hOsubset : (O : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyO
    -- Decompose the membership information.
    have hyK    : y ∈ interior (closure (interior A)) := hyO.1
    have hyNotB : y ∉ B := hyO.2
    -- From `hyK` we drop to the closure of `interior A`.
    have hy_cl : y ∈ closure (interior A) := interior_subset hyK
    -- We prove `y ∈ closure (interior (A \ B))` via the neighbourhood
    -- characterisation.
    refine
      (mem_closure_iff).2 ?_
    intro U hUopen hyU
    -- Shrink the neighbourhood so that it avoids `B`.
    have hUopen' : IsOpen (U ∩ (Bᶜ : Set X)) :=
      hUopen.inter hBclosed.isOpen_compl
    have hyU' : y ∈ U ∩ (Bᶜ : Set X) := by
      exact ⟨hyU, hyNotB⟩
    -- Since `y ∈ closure (interior A)`, this set meets `interior A`.
    obtain ⟨z, hzU', hzIntA⟩ :=
      (mem_closure_iff).1 hy_cl _ hUopen' hyU'
    -- Split the information on `z`.
    have hzU : z ∈ U := hzU'.1
    have hzNotB : z ∈ (Bᶜ : Set X) := hzU'.2
    -- Show that `z ∈ interior (A \ B)`.
    have hzIntDiff : z ∈ interior (A \ B) := by
      -- The open set `W := interior A ∩ Bᶜ` contains `z`
      -- and is contained in `A \ B`.
      have hWopen : IsOpen (interior A ∩ (Bᶜ : Set X)) :=
        isOpen_interior.inter hBclosed.isOpen_compl
      have hzW : z ∈ interior A ∩ (Bᶜ : Set X) := ⟨hzIntA, hzNotB⟩
      have hWsub : (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
        intro w hw
        rcases hw with ⟨hwIntA, hwNotB⟩
        exact ⟨interior_subset hwIntA, hwNotB⟩
      have h_nhds : (A \ B : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset (hWopen.mem_nhds hzW) hWsub
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Provide the required intersection witness.
    exact ⟨z, ⟨hzU, hzIntDiff⟩⟩
  ------------------------------------------------------------------
  -- Step 3: upgrade via `interior_maximal`.
  ------------------------------------------------------------------
  have hOsubsetInt :
      (O : Set X) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hOsubset hOopen
  exact hOsubsetInt hxO

theorem P1_prod_empty {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (∅ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (∅ : Set Y)) hA (by
      simpa using (P1_empty (X := Y))))

theorem P3_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (e '' A) := by
  classical
  -- The homeomorphism transports `interior (closure A)` as expected.
  have hImage :
      (e '' interior (closure A) : Set Y) =
        interior (closure (e '' A)) := by
    calc
      e '' interior (closure A)
          = interior (e '' closure A) := by
            simpa using e.image_interior (s := closure A)
      _ = interior (closure (e '' A)) := by
            simpa [e.image_closure (s := A)]
  ------------------------------------------------------------------
  -- Forward direction: `P3 A → P3 (e '' A)`.
  ------------------------------------------------------------------
  have forward : P3 A → P3 (e '' A) := by
    intro hP3
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure A) := hP3 hxA
    have : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
    simpa [hImage] using this
  ------------------------------------------------------------------
  -- Backward direction: `P3 (e '' A) → P3 A`.
  ------------------------------------------------------------------
  have backward : P3 (e '' A) → P3 A := by
    intro hP3img
    intro x hxA
    have h1 : e x ∈ interior (closure (e '' A)) :=
      hP3img ⟨x, hxA, rfl⟩
    have h2 : e x ∈ e '' interior (closure A) := by
      simpa [hImage] using h1
    rcases h2 with ⟨x', hx'int, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'int
  ------------------------------------------------------------------
  -- Assemble the equivalence.
  ------------------------------------------------------------------
  exact ⟨forward, backward⟩

theorem P1_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (e '' A) := by
  classical
  -- Auxiliary equality transporting `closure (interior A)` through the homeomorphism.
  have hImage :
      (e '' closure (interior A) : Set Y) =
        closure (interior (e '' A)) := by
    calc
      (e '' closure (interior A) : Set Y)
          = closure (e '' interior A) := by
              simpa using e.image_closure (s := interior A)
      _     = closure (interior (e '' A)) := by
        have hInt : (e '' interior A : Set Y) = interior (e '' A) := by
          simpa using e.image_interior (s := A)
        simpa [hInt]
  ------------------------------------------------------------------
  -- Forward direction: `P1 A → P1 (e '' A)`.
  ------------------------------------------------------------------
  have forward : P1 A → P1 (e '' A) := by
    intro hP1
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    have h_mem : e x ∈ (e '' closure (interior A) : Set Y) := ⟨x, hx_cl, rfl⟩
    simpa [hImage] using h_mem
  ------------------------------------------------------------------
  -- Backward direction: `P1 (e '' A) → P1 A`.
  ------------------------------------------------------------------
  have backward : P1 (e '' A) → P1 A := by
    intro hP1img
    intro x hxA
    have h1 : e x ∈ closure (interior (e '' A)) :=
      hP1img ⟨x, hxA, rfl⟩
    have h2 : e x ∈ (e '' closure (interior A) : Set Y) := by
      simpa [hImage] using h1
    rcases h2 with ⟨x', hx'cl, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'cl
  ------------------------------------------------------------------
  -- Assemble the equivalence.
  ------------------------------------------------------------------
  exact ⟨forward, backward⟩

theorem P2_basis_open {X} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ A) → P2 A := by
  intro hBasis
  intro x hxA
  -- Obtain an open neighbourhood whose closure stays inside `A`.
  rcases hBasis x hxA with ⟨U, hUopen, hxU, hUclosure⟩
  ------------------------------------------------------------------
  -- 1.  `U ⊆ A`.
  ------------------------------------------------------------------
  have hU_sub_A : (U : Set X) ⊆ A := by
    intro y hyU
    have : (y : X) ∈ closure U := subset_closure hyU
    exact hUclosure this
  ------------------------------------------------------------------
  -- 2.  `U ⊆ interior A`, hence `x ∈ interior A`.
  ------------------------------------------------------------------
  have hU_sub_intA : (U : Set X) ⊆ interior A := by
    intro y hyU
    have hA_nhds : (A : Set X) ∈ 𝓝 y :=
      Filter.mem_of_superset (hUopen.mem_nhds hyU) hU_sub_A
    exact (mem_interior_iff_mem_nhds).2 hA_nhds
  have hx_intA : x ∈ interior A := hU_sub_intA hxU
  ------------------------------------------------------------------
  -- 3.  `interior A ⊆ interior (closure (interior A))`.
  ------------------------------------------------------------------
  have hsubset :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  ------------------------------------------------------------------
  -- 4.  Conclude the desired membership.
  ------------------------------------------------------------------
  exact hsubset hx_intA

theorem P3_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  exact P3_prod (P3_prod hA hB) hC

theorem P1_setdiff {X} [TopologicalSpace X] {A B : Set X} : P1 A → IsClosed B → B ⊆ A → P1 (A \ B) := by
  intro hP1 hBclosed hBsub
  intro x hxDiff
  -- Decompose the membership information of `x`.
  rcases hxDiff with ⟨hxA, hxNotB⟩
  -- We will prove that every neighbourhood of `x` meets `interior (A \ B)`.
  have h_closure : x ∈ closure (interior (A \ B)) := by
    -- Use the neighbourhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Shrink `U` so that it avoids `B`.
    have hVopen : IsOpen (U ∩ (Bᶜ : Set X)) := hUopen.inter hBclosed.isOpen_compl
    have hxV : x ∈ U ∩ (Bᶜ : Set X) := by
      exact ⟨hxU, hxNotB⟩
    -- From `P1 A`, every neighbourhood of `x` meets `interior A`.
    have hP1_prop :=
      (mem_closure_iff).1 (hP1 hxA)
    -- Hence the shrunken neighbourhood meets `interior A`.
    rcases hP1_prop (U ∩ (Bᶜ : Set X)) hVopen hxV with
      ⟨y, ⟨hyV, hyIntA⟩⟩
    -- `y` lies in `U`.
    have hyU : y ∈ U := hyV.1
    -- `y` avoids `B`.
    have hyNotB : y ∈ (Bᶜ : Set X) := hyV.2
    ----------------------------------------------------------------
    -- Show that `y ∈ interior (A \ B)`.
    ----------------------------------------------------------------
    -- First, observe that `interior A ∩ Bᶜ` is open and contained in `A \ B`.
    have hOpen : IsOpen (interior A ∩ (Bᶜ : Set X)) :=
      isOpen_interior.inter hBclosed.isOpen_compl
    have hSub : (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
      intro z hz; exact ⟨interior_subset hz.1, hz.2⟩
    -- By maximality of the interior, this open set lies in `interior (A \ B)`.
    have hSubsetInt :
        (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ interior (A \ B) :=
      interior_maximal hSub hOpen
    -- Consequently, `y` belongs to `interior (A \ B)`.
    have hyIntDiff : y ∈ interior (A \ B) :=
      hSubsetInt ⟨hyIntA, hyNotB⟩
    -- Provide the required witness that `U` meets `interior (A \ B)`.
    exact ⟨y, ⟨hyU, hyIntDiff⟩⟩
  -- Finish the proof.
  exact h_closure

theorem P1_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  simpa using
    P1_prod (A := A ×ˢ B) (B := C)
      (P1_prod (A := A) (B := B) hA hB) hC

theorem P2_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  have hAB : P2 (A ×ˢ B) := P2_prod (A := A) (B := B) hA hB
  simpa using (P2_prod (A := A ×ˢ B) (B := C) hAB hC)

theorem P2_of_P1_P3 {X} [TopologicalSpace X] {A : Set X} : P1 A → P3 A → P2 A := by
  intro hP1 hP3
  intro x hxA
  -- `P3` gives `x ∈ interior (closure A)`.
  have hx_int_closureA : x ∈ interior (closure A) := hP3 hxA
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  -- Taking closures yields `closure A ⊆ closure (interior A)`.
  have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
    have h' : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using (closure_mono h')
  -- Monotonicity of `interior` upgrades the inclusion.
  have h_subset_int :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_subset
  -- Conclude the goal.
  exact h_subset_int hx_int_closureA

theorem P2_discrete {X} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P2 A := by
  have hAopen : IsOpen (A : Set X) := by
    simpa using isOpen_discrete (s := (A : Set X))
  exact P2_of_open (A := A) hAopen

theorem P2_subset_closure {X} [TopologicalSpace X] {A : Set X} : P2 A → (A : Set X) ⊆ closure (interior A) := by
  intro hP2 x hxA
  exact interior_subset (hP2 hxA)

theorem P3_nhds_basis {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∀ V ∈ 𝓝 x, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ U ⊆ closure A := by
  classical
  -- We use the already–proved characterisation of `P3` via open neighbourhoods.
  have h_open : P3 A ↔
      ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A :=
    P3_iff_forall_point (A := A)
  --------------------------------------------------------------------------
  -- We now establish the required equivalence.
  --------------------------------------------------------------------------
  constructor
  · -- `P3 A →` neighbourhood‐basis statement.
    intro hP3
    -- Reformulate `hP3` in terms of open neighbourhoods.
    have hP3_open := (h_open).1 hP3
    -- Fix a point `x ∈ A` and a neighbourhood `V` of `x`.
    intro x hxA V hV
    -- Obtain an open set `U₁ ⊆ closure A` containing `x`.
    rcases hP3_open x hxA with ⟨U₁, hU₁open, hxU₁, hU₁sub⟩
    -- From `V ∈ 𝓝 x`, pick an open set `V₀` with `x ∈ V₀ ⊆ V`.
    rcases mem_nhds_iff.1 hV with ⟨V₀, hV₀sub, hV₀open, hxV₀⟩
    -- Intersect the two open sets.
    refine ⟨U₁ ∩ V₀, hU₁open.inter hV₀open, ⟨hxU₁, hxV₀⟩, ?_, ?_⟩
    · -- `U₁ ∩ V₀ ⊆ V`
      intro y hy
      exact hV₀sub hy.2
    · -- `U₁ ∩ V₀ ⊆ closure A`
      intro y hy
      exact hU₁sub hy.1
  · -- Converse: neighbourhood‐basis statement → `P3 A`.
    intro hBasis
    -- Build the open‐neighbourhood formulation required by `h_open`.
    have h_open_form :
        ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
      intro x hxA
      -- Apply the basis property with the trivial neighbourhood `univ`.
      rcases hBasis x hxA Set.univ Filter.univ_mem with
        ⟨U, hUopen, hxU, _hUsubUniv, hUsub_closure⟩
      exact ⟨U, hUopen, hxU, hUsub_closure⟩
    -- Translate back to `P3 A`.
    exact (h_open).2 h_open_form

theorem P2_sImage {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P2 A) : P2 {x | ∃ A ∈ ℱ, x ∈ A} := by
  simpa using (P2_sUnion (X := X) (ℱ := ℱ) h)