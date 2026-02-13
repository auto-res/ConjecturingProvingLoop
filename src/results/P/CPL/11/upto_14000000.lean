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


theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hA hx)

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  simpa [hA.interior_eq] using interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` is in `A`
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_sub :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      exact h_sub hx_closure
  | inr hxB =>
      -- `x` is in `B`
      have hx_closure : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_sub :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact h_sub hx_closure

theorem exists_open_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ U ⊆ A := by
  refine ⟨interior A, isOpen_interior, ?_⟩
  exact interior_subset

theorem P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure A ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    have h₂ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact le_antisymm h₂ h₁
  · intro h_eq
    have : (A : Set X) ⊆ closure (interior A) := by
      have hsub : (A : Set X) ⊆ closure A := subset_closure
      simpa [h_eq.symm] using hsub
    exact this

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- `A` is contained in the interior of its closure since it is open.
  have hx' : x ∈ interior (closure A) := by
    have hsub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact hsub hx
  simpa [hA.interior_eq] using hx'

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P3 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hsub hx'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- We show that `interior (closure (interior A))` is contained in
      -- `interior (closure (interior (A ∪ B)))`.
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- First, relate the two closures.
        have h_closure :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- `interior A` is contained in `interior (A ∪ B)`
          -- because it is an open subset of `A ∪ B`.
          have h_int :
              (interior A : Set X) ⊆ interior (A ∪ B) := by
            have h_aux : (interior A : Set X) ⊆ (A ∪ B) := by
              intro y hy
              exact Or.inl (interior_subset hy)
            exact interior_maximal h_aux isOpen_interior
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      -- `x` comes from `B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      -- Similar containment for the `B` side.
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int :
              (interior B : Set X) ⊆ interior (A ∪ B) := by
            have h_aux : (interior B : Set X) ⊆ (A ∪ B) := by
              intro y hy
              exact Or.inr (interior_subset hy)
            exact interior_maximal h_aux isOpen_interior
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB'

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro y hy
            exact Or.inl hy)
        exact interior_mono hcl
      exact hsubset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro y hy
            exact Or.inr hy)
        exact interior_mono hcl
      exact hsubset hxB'

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- `A ⊆ U`
    exact hA
  · -- `closure U = closure A`
    apply le_antisymm
    · -- `closure U ⊆ closure A`
      have h₁ : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      have h₂ : closure (interior (closure A)) ⊆ closure A := by
        simpa [closure_closure] using closure_mono h₁
      exact h₂
    · -- `closure A ⊆ closure U`
      have h₁ : (A : Set X) ⊆ interior (closure A) := hA
      have h₂ : closure A ⊆ closure (interior (closure A)) := by
        simpa using closure_mono h₁
      exact h₂

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `x` is in `s i`, hence in `closure (interior (s i))`
  have hx_closure : x ∈ closure (interior (s i)) := (h i) hx_i
  -- show that this closure is contained in the desired one
  have h_subset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    -- `interior (s i)` is contained in `interior (⋃ j, s j)`
    have h_int : (interior (s i) : Set X) ⊆ interior (⋃ j, s j) := by
      have h_s : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_s
    exact closure_mono h_int
  exact h_subset hx_closure

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- from `P3 (s i)` we know `x` lies in `interior (closure (s i))`
  have hx' : x ∈ interior (closure (s i)) := (h i) hx_i
  -- we now relate this interior to the desired one
  have h_subset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    have h_closure : closure (s i) ⊆ closure (⋃ j, s j) := by
      refine closure_mono ?_
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_closure
  exact h_subset hx'

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx' : x ∈ interior (closure (interior (s i))) := (h i) hx_i
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    have h_closure :
        closure (interior (s i)) ⊆
          closure (interior (⋃ j, s j)) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      have h_int : (interior (s i) : Set X) ⊆ interior (⋃ j, s j) :=
        interior_mono h_sub
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx'

theorem exists_dense_open_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ U ⊆ A := by
  refine ⟨interior A, isOpen_interior, ?_, interior_subset⟩
  simpa using (P1_iff_closure_interior_eq).1 hA

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  exact False.elim hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem exists_open_dense_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  -- We take `U = interior (closure (interior A))`
  refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
  · -- `A ⊆ U`
    exact hA
  · -- `closure U = closure A`
    apply le_antisymm
    · -- `closure U ⊆ closure A`
      have h₁ : (interior (closure (interior A)) : Set X) ⊆ closure A := by
        intro x hx
        -- From `hx : x ∈ U` we get `x ∈ closure (interior A)`
        have hx' : x ∈ closure (interior A) :=
          (interior_subset :
            interior (closure (interior A)) ⊆ closure (interior A)) hx
        -- And `closure (interior A) ⊆ closure A`
        have hcl :
            (closure (interior A) : Set X) ⊆ closure A :=
          closure_mono (interior_subset : (interior A : Set X) ⊆ A)
        exact hcl hx'
      have : closure (interior (closure (interior A))) ⊆ closure A := by
        simpa [closure_closure] using closure_mono h₁
      exact this
    · -- `closure A ⊆ closure U`
      have h₂ : (A : Set X) ⊆ interior (closure (interior A)) := hA
      have : closure A ⊆ closure (interior (closure (interior A))) :=
        closure_mono h₂
      simpa using this

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure A) := by
  intro x hx
  -- We first prove that `closure A ⊆ closure (interior (closure A))`.
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- It suffices to show `A ⊆ closure (interior (closure A))`
    -- and then use `closure_minimal`.
    have hA' : (A : Set X) ⊆ closure (interior (closure A)) := by
      intro y hy
      -- From `P1 A` we know `y ∈ closure (interior A)`.
      have hy₁ : y ∈ closure (interior A) := hA hy
      -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
      have hint : (interior A : Set X) ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      -- Taking closures preserves inclusion.
      have hcl : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
        closure_mono hint
      exact hcl hy₁
    -- Apply the universal property of the closure.
    exact closure_minimal hA' isClosed_closure
  exact hsubset hx

theorem exists_open_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U := by
  exact ⟨interior (closure (A : Set X)), isOpen_interior, hA⟩

theorem exists_closed_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ C, IsClosed C ∧ A ⊆ C := by
  exact ⟨closure A, isClosed_closure, subset_closure⟩

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P1 A) : P1 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hPA : P1 A := h A hA_mem
  have hx_closure : x ∈ closure (interior A) := hPA hxA
  -- `A ⊆ ⋃₀ 𝒜`
  have h_subA : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  -- hence `interior A ⊆ interior (⋃₀ 𝒜)`
  have h_int : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) :=
    interior_mono h_subA
  -- taking closures preserves inclusion
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int
  exact h_subset hx_closure

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P2 A) : P2 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2 : P2 A := h A hA_mem
  have hx' : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    have h_closure :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
      have h_int : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) := by
        have h_subA : (A : Set X) ⊆ ⋃₀ 𝒜 := by
          intro y hy
          exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
        exact interior_mono h_subA
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx'

theorem P1_of_closed_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h₁ : IsClosed A) (h₂ : closure (interior A) = A) : P1 A := by
  intro x hx
  simpa [h₂] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  simpa [hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A) hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem exists_closed_superset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ C, IsClosed C ∧ A ⊆ C := by
  exact ⟨closure A, isClosed_closure, subset_closure⟩

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → (P1 A ↔ A ⊆ closure A) := by
  intro hA
  simpa [P1, hA.interior_eq]

theorem exists_open_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro _ _; trivial
  · exact P1_univ

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (mem_univ x)

theorem exists_compact_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  intro x hx
  cases hx

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h, interior_univ] using this

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  simpa using (P1_of_open (A := interior A) isOpen_interior)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  simpa using (P2_of_open (A := interior A) isOpen_interior)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  exact
    (interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior) hx

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  exact P1_closure (P1_of_P2 hA)

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  -- First, show that `closure A = Set.univ`.
  have h_dense_closure : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- `closure (interior A)` is all of `X` by hypothesis and is contained in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h] using
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
    -- Trivially, `closure A ⊆ Set.univ`.
    have h_subset_univ : (closure (A : Set X)) ⊆ (Set.univ : Set X) := by
      intro x hx
      trivial
    exact le_antisymm h_subset_univ h_univ_subset
  -- With `closure A = Set.univ`, apply the existing lemma `P3_of_dense`.
  exact P3_of_dense (X := X) (A := A) h_dense_closure

theorem exists_open_between_interior_and_closure {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ interior A ⊆ U ∧ U ⊆ closure A := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  ·
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    simpa using this
  ·
    exact interior_subset

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3 : P3 A := h A hA_mem
  have hx' : x ∈ interior (closure A) := hP3 hxA
  have h_subset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒜)) := by
    have h_closure :
        (closure A : Set X) ⊆ closure (⋃₀ 𝒜) := by
      refine closure_mono ?_
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact interior_mono h_closure
  exact h_subset hx'

theorem closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : closure A = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hsubset : (A : Set X) ⊆ interior (closure A) := hA
    exact closure_mono hsubset
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hsubset : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    simpa using closure_mono hsubset

theorem interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : interior (closure (interior A)) = interior (closure A) := by
  -- From `P1 A` we get equality of the two closures
  have h_eq : closure (interior A) = closure A :=
    (P1_iff_closure_interior_eq).1 hA
  -- Taking interiors of both sides yields the desired result
  simpa using congrArg interior h_eq

theorem dense_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior A) = closure A := by
  exact (P1_iff_closure_interior_eq).1 (P1_of_P2 hA)

theorem P2_iff_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro h2
    exact ⟨P1_of_P2 h2, P3_of_P2 h2⟩
  · rintro ⟨h1, h3⟩
    intro x hx
    have hx3 : x ∈ interior (closure A) := h3 hx
    have h_eq : interior (closure (interior A)) = interior (closure A) :=
      interior_closure_eq_of_P1 h1
    simpa [h_eq] using hx3

theorem P3_of_open_dense_subset {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) (h_dense : closure U = closure A) (h_sub : A ⊆ U) : P3 A := by
  intro x hxA
  -- `A ⊆ U`, hence `x ∈ U`
  have hxU : x ∈ U := h_sub hxA
  -- Because `U` is open and contained in `closure A`, we have `U ⊆ interior (closure A)`.
  have hU_interior : (U : Set X) ⊆ interior (closure A) := by
    -- First, show `U ⊆ closure A`.
    have hU_closure : (U : Set X) ⊆ closure A := by
      -- We always have `U ⊆ closure U`; rewrite using `h_dense`.
      have : (U : Set X) ⊆ closure U := subset_closure
      simpa [h_dense] using this
    exact interior_maximal hU_closure hU
  -- Conclude that `x ∈ interior (closure A)`.
  exact hU_interior hxU

theorem interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : interior (closure (interior A)) = interior (closure A) := by
  simpa using interior_closure_eq_of_P1 (P1_of_P2 hA)

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : P1 (e '' A) := by
  -- Unfold the goal: we need `e '' A ⊆ closure (interior (e '' A))`.
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1 A` we have `x ∈ closure (interior A)`.
  have hx_closure : x ∈ closure (interior A) := hA hxA
  -- First show `e x ∈ closure (e '' interior A)`.
  have h1 : (e x) ∈ closure (e '' interior A) := by
    -- Use the characterization of closure via open neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro V hV hxV
    -- Consider the preimage of `V` under `e`.
    have h_pre_open : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
    have hx_pre : x ∈ e ⁻¹' V := by
      change e x ∈ V
      simpa using hxV
    -- Since `x` is in the closure of `interior A`, this intersection is non-empty.
    have h_nonempty : ((e ⁻¹' V) ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hx_closure _ h_pre_open hx_pre
    rcases h_nonempty with ⟨z, ⟨hzV, hzInt⟩⟩
    -- Map the witness forward with `e`.
    have hzV'   : e z ∈ V                := hzV
    have hzInt' : e z ∈ e '' interior A := ⟨z, hzInt, rfl⟩
    exact ⟨e z, ⟨hzV', hzInt'⟩⟩
  -- Next, show `e '' interior A ⊆ interior (e '' A)`.
  have h_subset : (e '' interior A : Set _) ⊆ interior (e '' A) := by
    -- It is an open subset of `e '' A`.
    have h_incl : (e '' interior A : Set _) ⊆ e '' A := by
      rintro y ⟨x, hxInt, rfl⟩
      exact ⟨x, interior_subset hxInt, rfl⟩
    have h_open : IsOpen (e '' interior A) := by
      simpa using e.isOpenMap.image (s := interior A) isOpen_interior
    exact interior_maximal h_incl h_open
  -- Taking closures preserves inclusion.
  have h_subset' : closure (e '' interior A) ⊆ closure (interior (e '' A)) :=
    closure_mono h_subset
  -- Finish.
  exact h_subset' h1

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  -- First, turn `hA` into `P1 A` and `P3 A`.
  have hP1A : P1 A := P1_of_P2 hA
  have hP3A : P3 A := P3_of_P2 hA
  -- Transport `P1` along the homeomorphism.
  have hP1Img : P1 (e '' A) := P1_image_homeomorph (e := e) hP1A
  -- We now prove `P3 (e '' A)`.
  have hP3Img : P3 (e '' A) := by
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    -- `x` lies in the interior of `closure A`.
    have hxInt : x ∈ interior (closure (A : Set X)) := hP3A hxA
    -- Show that `e x` belongs to the interior of the closure of `e '' A`.
    -- First, place it in an auxiliary open set.
    have hxImage : (e x) ∈ (e '' interior (closure (A : Set X))) :=
      ⟨x, hxInt, rfl⟩
    -- This open set sits inside `interior (closure (e '' A))`.
    have h_subset :
        (e '' interior (closure (A : Set X)) : Set Y) ⊆
          interior (closure (e '' (A : Set X))) := by
      -- Step 1: it is contained in `closure (e '' A)`.
      have h_incl :
          (e '' interior (closure (A : Set X)) : Set Y) ⊆
            closure (e '' (A : Set X)) := by
        rintro y ⟨x, hxInt', rfl⟩
        -- From `hxInt'` we know `x ∈ closure A`.
        have hx_closure : x ∈ closure (A : Set X) := interior_subset hxInt'
        -- Show `e x` is in the desired closure using the neighbourhood
        -- characterisation.
        have : (e x) ∈ closure (e '' (A : Set X)) := by
          refine (mem_closure_iff).2 ?_
          intro V hV hxV
          -- Pull back the open neighbourhood along `e`.
          have pre_open : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
          have hx_pre : x ∈ e ⁻¹' V := by
            change e x ∈ V
            simpa using hxV
          -- Use that `x ∈ closure A`.
          have h_ne : ((e ⁻¹' V) ∩ (A : Set X)).Nonempty :=
            (mem_closure_iff).1 hx_closure _ pre_open hx_pre
          rcases h_ne with ⟨z, ⟨hzV, hzA⟩⟩
          exact ⟨e z, ⟨hzV, ⟨z, hzA, rfl⟩⟩⟩
        exact this
      -- Step 2: the set is open because `e` is an open map.
      have h_open : IsOpen (e '' interior (closure (A : Set X))) := by
        simpa using
          e.isOpenMap.image (s := interior (closure (A : Set X))) isOpen_interior
      -- Conclude using the maximality property of interiors.
      exact interior_maximal h_incl h_open
    exact h_subset hxImage
  -- Combine `P1` and `P3` for the image, then use the characterisation of `P2`.
  exact (P2_iff_P1_P3).2 ⟨hP1Img, hP3Img⟩

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P3 A` we get that `x` lies in the interior of `closure A`.
  have hxInt : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Consider the image of this interior point.
  have hxImage : (e x) ∈ (e '' interior (closure (A : Set X))) :=
    ⟨x, hxInt, rfl⟩
  -- We show that the whole image of `interior (closure A)` sits inside
  -- `interior (closure (e '' A))`.
  have h_subset :
      (e '' interior (closure (A : Set X)) : Set Y) ⊆
        interior (closure (e '' (A : Set X))) := by
    -- First, prove containment in the closure.
    have h_incl :
        (e '' interior (closure (A : Set X)) : Set Y) ⊆
          closure (e '' (A : Set X)) := by
      rintro z ⟨x', hx', rfl⟩
      have hx'cl : (x' : X) ∈ closure (A : Set X) := interior_subset hx'
      -- Show that `e x'` is in the desired closure.
      have : (e x') ∈ closure (e '' (A : Set X)) := by
        refine (mem_closure_iff).2 ?_
        intro V hV hxV
        -- Pull back the neighbourhood along `e`.
        have hPreOpen : IsOpen (e ⁻¹' V) := hV.preimage e.continuous_toFun
        have hxPre : x' ∈ e ⁻¹' V := by
          change e x' ∈ V
          simpa using hxV
        -- Use that `x' ∈ closure A`.
        have h_nonempty : ((e ⁻¹' V) ∩ (A : Set X)).Nonempty :=
          (mem_closure_iff).1 hx'cl _ hPreOpen hxPre
        rcases h_nonempty with ⟨t, ⟨htV, htA⟩⟩
        exact ⟨e t, ⟨htV, ⟨t, htA, rfl⟩⟩⟩
      simpa using this
    -- The image set is open because `e` is an open map.
    have h_open : IsOpen (e '' interior (closure (A : Set X))) := by
      simpa using
        e.isOpenMap.image (s := interior (closure (A : Set X))) isOpen_interior
    -- Apply maximality of the interior.
    exact interior_maximal h_incl h_open
  exact h_subset hxImage

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := by
  exact (P2_iff_P1_P3).2 ⟨h1, h3⟩

theorem exists_closed_superset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ C, IsClosed C ∧ A ⊆ C := by
  simpa using exists_closed_superset_of_P1 (A := A) (hA := P1_of_P2 hA)

theorem P3_iff_dense_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ closure A = closure (interior (closure A)) ∧ A ⊆ interior (closure A) := by
  constructor
  · intro hP3
    exact ⟨closure_eq_of_P3 (A := A) hP3, hP3⟩
  · rintro ⟨_, h_subset⟩
    exact h_subset

theorem P1_iff_dense_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using (P1_iff_closure_interior_eq (A := A))

theorem P1_subsingleton (X : Type*) [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  -- In a subsingleton space, any nonempty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence `closure (interior A)` is `univ`, so the claim follows.
  have : x ∈ closure (interior A) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA_univ, interior_univ, closure_univ] using this
  exact this

theorem exists_open_dense_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = Set.univ := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro x hx; trivial
  · simpa using closure_univ

theorem P1_iff_dense_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) ∧ A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    have h_eq := (P1_iff_closure_interior_eq (A := A)).1 hP1
    exact ⟨h_eq.symm, hP1⟩
  · rintro ⟨_, h_subset⟩
    exact h_subset

theorem P2_of_P3_and_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_dense : closure (interior A) = closure A) : P2 A := by
  have h1 : P1 A := (P1_iff_closure_interior_eq (A := A)).2 h_dense
  exact P2_of_P1_and_P3 h1 h3

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate belongs to the corresponding closure.
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` is in the product of these closures, which equals the closure
  -- of the product of the interiors.
  have h_mem_closure_prod : p ∈ closure ((interior A) ×ˢ (interior B)) := by
    have : p ∈ (closure (interior A) ×ˢ closure (interior B)) := by
      exact ⟨hx, hy⟩
    simpa [closure_prod_eq] using this
  -- The product of the interiors sits inside the interior of `A ×ˢ B`.
  have h_subset :
      ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`.
    have h_incl :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro z hz
      rcases hz with ⟨hzA, hzB⟩
      exact ⟨interior_subset hzA, interior_subset hzB⟩
    -- It is an open set.
    have h_open :
        IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
      (isOpen_interior.prod isOpen_interior)
    -- Therefore it is contained in the interior of `A ×ˢ B`.
    exact interior_maximal h_incl h_open
  -- Taking closures preserves inclusion.
  have h_closure_subset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_subset
  exact h_closure_subset h_mem_closure_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P2` to each coordinate.
  have hx : p.1 ∈ interior (closure (interior A)) := hA hpA
  have hy : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- The point `p` lies in the following open rectangle.
  have h_mem :
      p ∈
        ((interior (closure (interior A))) ×ˢ
          (interior (closure (interior B)))) := by
    exact ⟨hx, hy⟩
  -- This rectangle is open.
  have h_open :
      IsOpen
        ((interior (closure (interior A))) ×ˢ
          (interior (closure (interior B))) : Set (X × Y)) :=
    (isOpen_interior.prod isOpen_interior)
  -- Show the rectangle is contained in the closure of
  -- `(interior A) ×ˢ (interior B)`.
  have h_sub :
      ((interior (closure (interior A))) ×ˢ
        (interior (closure (interior B))) : Set (X × Y)) ⊆
        closure ((interior A) ×ˢ (interior B)) := by
    intro z hz
    rcases hz with ⟨hz1, hz2⟩
    have hz1_cl : z.1 ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hz1
    have hz2_cl : z.2 ∈ closure (interior B) :=
      (interior_subset : interior (closure (interior B)) ⊆ closure (interior B)) hz2
    have : (z : X × Y) ∈ (closure (interior A) ×ˢ closure (interior B)) :=
      ⟨hz1_cl, hz2_cl⟩
    simpa [closure_prod_eq] using this
  -- Hence the rectangle sits inside the desired interior.
  have h_sub_int :
      ((interior (closure (interior A))) ×ˢ
        (interior (closure (interior B))) : Set (X × Y)) ⊆
        interior (closure ((interior A) ×ˢ (interior B))) :=
    interior_maximal h_sub h_open
  -- Conclude for the given point `p`.
  have h_final :
      p ∈ interior (closure ((interior A) ×ˢ (interior B))) :=
    h_sub_int h_mem
  -- Rewrite using `interior_prod_eq` to match the goal.
  simpa [interior_prod_eq] using h_final

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate lies in the interior of the corresponding closure.
  have hA_int : p.1 ∈ interior (closure (A : Set X)) := hA hpA
  have hB_int : p.2 ∈ interior (closure (B : Set Y)) := hB hpB
  -- Hence `p` lies in the following open rectangle.
  have h_mem :
      p ∈
        ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y)))) := by
    exact ⟨hA_int, hB_int⟩
  -- This rectangle is open.
  have h_open :
      IsOpen
        ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) :=
    (isOpen_interior.prod isOpen_interior)
  -- Show the rectangle is contained in the closure of `A ×ˢ B`.
  have h_incl :
      ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) ⊆
        closure (A ×ˢ B) := by
    intro z hz
    rcases hz with ⟨hzA, hzB⟩
    have hzA_cl : (z.1 : X) ∈ closure (A : Set X) :=
      (interior_subset :
        interior (closure (A : Set X)) ⊆ closure A) hzA
    have hzB_cl : (z.2 : Y) ∈ closure (B : Set Y) :=
      (interior_subset :
        interior (closure (B : Set Y)) ⊆ closure B) hzB
    have : (z : X × Y) ∈ (closure (A : Set X)) ×ˢ (closure (B : Set Y)) :=
      ⟨hzA_cl, hzB_cl⟩
    simpa [closure_prod_eq] using this
  -- Therefore the rectangle sits inside the desired interior.
  have h_sub_int :
      ((interior (closure (A : Set X))) ×ˢ
          (interior (closure (B : Set Y))) : Set (X × Y)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal h_incl h_open
  exact h_sub_int h_mem

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  have h_univ : P2 (Set.univ : Set Y) := P2_univ
  simpa using
    (P2_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P3 B) : P3 ((Set.univ : Set X) ×ˢ B) := by
  simpa using
    (P3_prod (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := B)
      (P3_univ (X := X)) hB)

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P1 B) : P1 (e ⁻¹' B) := by
  -- First, transport the statement to the inverse homeomorphism.
  have h_img : P1 (e.symm '' (B : Set Y)) := by
    simpa using (P1_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify the image with the preimage.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- After `rfl`, we must prove `e (e.symm y) ∈ B`, which simplifies to `y ∈ B`.
      simpa using hyB
    · intro hx
      -- `hx : e x ∈ B`
      exact ⟨e x, hx, by
        simp⟩
  -- Conclude using the previously obtained result and the set equality.
  simpa [h_eq] using h_img

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P2 B) : P2 (e ⁻¹' B) := by
  -- Obtain `P2` for the image of `B` under `e.symm`.
  have h_img : P2 (e.symm '' (B : Set Y)) := by
    simpa using (P2_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify that image with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Transport the property along the set equality.
  simpa [h_eq] using h_img

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P3 B) : P3 (e ⁻¹' B) := by
  -- First, transport `P3` along the homeomorphism `e.symm`.
  have h_img : P3 (e.symm '' (B : Set Y)) := by
    simpa using (P3_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify that image with the desired preimage.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- After `rfl`, the goal becomes `e (e.symm y) ∈ B`, which reduces to `y ∈ B`.
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp⟩
  -- Transport `P3` along the set equality.
  simpa [h_eq] using h_img

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P2 B) : P2 ((Set.univ : Set X) ×ˢ B) := by
  have h_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := B) h_univ hB)

theorem P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  have h_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y)
      (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P1_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ P2 (∅ : Set X) := by
  constructor
  · intro _; exact P2_empty (X := X)
  · intro _; exact P1_empty (X := X)

theorem P3_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ P2 (Set.univ : Set X) := by
  constructor
  · intro _
    exact P2_univ (X := X)
  · intro _
    exact P3_univ (X := X)

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior A) = closure (interior (closure A)) := by
  calc
    closure (interior A)
        = closure A := dense_closure_of_P2 (A := A) hA
    _ = closure (interior (closure A)) :=
      (closure_eq_of_P3 (A := A) (hA := P3_of_P2 hA))

theorem exists_closed_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ C, IsClosed C ∧ C ⊆ A := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_⟩
  intro x hx
  cases hx

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  have h_univ : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem exists_open_dense_superset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = Set.univ := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro x hx
    trivial
  · simpa using closure_univ

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P1` for the product `B ×ˢ C` (a subset of `Y × Z`).
  have hBC : P1 (B ×ˢ C) :=
    P1_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P1_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P2` for the product `B ×ˢ C`.
  have hBC : P2 (B ×ˢ C) :=
    P2_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P2_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P3` for the product `B ×ˢ C`.
  have hBC : P3 (B ×ˢ C) :=
    P3_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P3_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)

theorem P1_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  exact Set.empty_subset _

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P3 (A ×ˢ B)) : P3 (B ×ˢ A) := by
  -- Define the swapping homeomorphism explicitly.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- Transport `P3` along this homeomorphism.
  have hImage : P3 (e '' (A ×ˢ B : Set (X × Y))) :=
    P3_image_homeomorph (e := e) (A := A ×ˢ B) h
  -- Identify the image with `B ×ˢ A`.
  have hEq :
      (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · -- Forward inclusion.
      rintro ⟨x, hxAB, rfl⟩
      rcases hxAB with ⟨hxA, hxB⟩
      exact And.intro hxB hxA
    · -- Reverse inclusion.
      intro hp
      rcases hp with ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact And.intro hpA hpB      -- membership in `A ×ˢ B`
      · -- `e` swaps the coordinates, so this is the required equality.
        simpa [e] using rfl
  -- Conclude using the set equality.
  simpa [hEq] using hImage

theorem P1_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P1 B) : P1 ((Set.univ : Set X) ×ˢ B) := by
  have h_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) h_univ hB)

theorem P2_iff_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ closure (interior A) = closure A ∧ A ⊆ interior (closure A) := by
  constructor
  · intro h2
    have hclosure : closure (interior (A : Set X)) = closure A :=
      dense_closure_of_P2 (A := A) h2
    have hsubset : (A : Set X) ⊆ interior (closure A) :=
      P3_of_P2 h2
    exact ⟨hclosure, hsubset⟩
  · rintro ⟨hclosure, hsubset⟩
    have h1 : P1 A :=
      (P1_iff_closure_interior_eq (A := A)).2 hclosure
    have h3 : P3 A := hsubset
    exact P2_of_P1_and_P3 h1 h3

theorem P1_of_P3_and_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_subset : interior (closure A) ⊆ A) : P1 A := by
  -- First, combine the two inclusions into an equality.
  have h_eq : (A : Set X) = interior (closure (A : Set X)) :=
    Set.Subset.antisymm h3 h_subset
  -- Hence `A` is open, since it coincides with an open set.
  have hA_open : IsOpen (A : Set X) := by
    simpa [h_eq.symm] using
      (isOpen_interior : IsOpen (interior (closure (A : Set X))))
  -- Open sets satisfy `P1`.
  exact P1_of_open (A := A) hA_open

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (A ×ˢ B) ↔ P2 (B ×ˢ A) := by
  -- Define the swapping homeomorphism.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- `e` maps `A ×ˢ B` to `B ×ˢ A`.
  have hEq :
      (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · rintro ⟨x, hxAB, rfl⟩
      rcases hxAB with ⟨hxA, hxB⟩
      exact ⟨hxB, hxA⟩
    · intro hp
      rcases hp with ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simpa [e] using rfl
  -- `e.symm` (which is `e`) maps `B ×ˢ A` back to `A ×ˢ B`.
  have hEq' :
      (e.symm '' (B ×ˢ A : Set (Y × X))) = (A ×ˢ B : Set (X × Y)) := by
    ext p
    constructor
    · rintro ⟨x, hxBA, rfl⟩
      rcases hxBA with ⟨hxB, hxA⟩
      exact ⟨hxA, hxB⟩
    · intro hp
      rcases hp with ⟨hpA, hpB⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpB, hpA⟩
      · simpa [e] using rfl
  -- Build the equivalence.
  constructor
  · intro hAB
    have hImage : P2 (e '' (A ×ˢ B : Set (X × Y))) :=
      P2_image_homeomorph (e := e) (A := A ×ˢ B) hAB
    simpa [hEq] using hImage
  · intro hBA
    have hImage : P2 (e.symm '' (B ×ˢ A : Set (Y × X))) :=
      P2_image_homeomorph (e := e.symm) (A := B ×ˢ A) hBA
    simpa [hEq'] using hImage

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P1 (A ×ˢ B)) : P1 (B ×ˢ A) := by
  -- Define the homeomorphism that swaps the two coordinates.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- Transport `P1` along this homeomorphism.
  have hImage : P1 (e '' (A ×ˢ B : Set (X × Y))) :=
    P1_image_homeomorph (e := e) (A := A ×ˢ B) h
  -- Identify the image with `B ×ˢ A`.
  have hEq : (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · -- Forward direction.
      rintro ⟨q, hqAB, rfl⟩
      rcases hqAB with ⟨hqA, hqB⟩
      exact And.intro hqB hqA
    · -- Reverse direction.
      intro hpBA
      rcases hpBA with ⟨hpB, hpA⟩
      refine ⟨(p.snd, p.fst), ?_, ?_⟩
      · exact And.intro hpA hpB
      · -- `e` swaps the coordinates, sending `(p.snd, p.fst)` to `p`.
        simp [e, Homeomorph.prodComm]      
  -- Conclude using the set equality.
  simpa [hEq] using hImage

theorem P1_prod_empty_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 ((∅ : Set X) ×ˢ B) := by
  intro x hx
  rcases hx with ⟨hFalse, _⟩
  cases hFalse

theorem P2_prod_empty_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hFalse⟩
  cases hFalse

theorem P3_iff_open_superset {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  constructor
  · intro hA
    exact exists_open_dense_subset_of_P3 hA
  · rintro ⟨U, hU_open, hAU, hclosure⟩
    exact P3_of_open_dense_subset hU_open hclosure hAU

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ×ˢ B ×ˢ C ×ˢ D) := by
  -- First, obtain `P3` for the product `B ×ˢ C ×ˢ D`.
  have hBCD : P3 (B ×ˢ C ×ˢ D) :=
    P3_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` using `P3_prod`.
  simpa using
    (P3_prod (A := A) (B := (B ×ˢ C ×ˢ D)) hA hBCD)

theorem P2_subsingleton (X : Type*) [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  -- In a subsingleton space, every element equals `x`, so `A = univ`.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence the target interior is `univ`, so the inclusion holds.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, interior_univ, closure_univ] using this

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure (interior A)) := by
  -- `P1` holds for `interior A`.
  have h_int : P1 (interior A) := P1_interior (A := A)
  -- Hence it also holds for the closure of `interior A`.
  simpa using (P1_closure (A := interior A) h_int)

theorem exists_compact_open_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ IsOpen K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, isOpen_empty, ?_⟩
  intro x hx
  cases hx

theorem P3_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) (hE : P3 E) : P3 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E) := by
  -- First, obtain `P3` for the product `B ×ˢ C ×ˢ D ×ˢ E`.
  have hBCDE : P3 (B ×ˢ C ×ˢ D ×ˢ E) :=
    P3_prod_four (A := B) (B := C) (C := D) (D := E) hB hC hD hE
  -- Combine with `A` using `P3_prod`.
  simpa using
    (P3_prod (A := A) (B := (B ×ˢ C ×ˢ D ×ˢ E)) hA hBCDE)

theorem P1_of_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior A) : P1 A := by
  intro x hx
  -- From `x ∈ A` we have `x ∈ closure A`.
  have hx_int : x ∈ interior A := h (subset_closure hx)
  -- And `interior A ⊆ closure (interior A)`.
  exact (subset_closure : (interior A : Set X) ⊆ closure (interior A)) hx_int

theorem P2_prod_mixed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (interior (Set.univ : Set Y))) := by
  simpa [interior_univ] using
    (P2_prod_left (X := X) (Y := Y) (A := A) hA)

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_closed : IsClosed A) : P1 A := by
  intro x hxA
  -- `x` is in the interior of the closure of `A`.
  have hxIntClosure : x ∈ interior (closure (A : Set X)) := h3 hxA
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : (closure (A : Set X)) = A := h_closed.closure_eq
  -- Hence `x` is in `interior A`.
  have hxInt : x ∈ interior (A : Set X) := by
    simpa [h_closure_eq] using hxIntClosure
  -- The interior of `A` is contained in `closure (interior A)`.
  exact (subset_closure : (interior A : Set X) ⊆ closure (interior A)) hxInt

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  exact ⟨fun _ => P2_of_open (A := A) hA,
         fun _ => P1_of_open (A := A) hA⟩

theorem P2_prod_snd_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 ((interior (Set.univ : Set X)) ×ˢ A) := by
  simpa [interior_univ] using
    (P2_prod_right (X := X) (Y := X) (B := A) hA)

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Next, combine this with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite using associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P2_antisymm {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hBA : B ⊆ A) (hA : P2 A) : P2 B := by
  have h_eq : (A : Set X) = B := Set.Subset.antisymm hAB hBA
  simpa [h_eq] using hA

theorem P1_prod_six {U V W X Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} {F : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) (hE : P1 E) (hF : P1 F) : P1 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
  -- Step 1: combine `E` and `F`.
  have hEF : P1 (E ×ˢ F) :=
    P1_prod (A := E) (B := F) hE hF
  -- Step 2: add `D`.
  have hDEF : P1 (D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := D) (B := (E ×ˢ F)) hD hEF)
  -- Step 3: add `C`.
  have hCDEF : P1 (C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := C) (B := (D ×ˢ E ×ˢ F)) hC hDEF)
  -- Step 4: add `B`.
  have hBCDEF : P1 (B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := B) (B := (C ×ˢ D ×ˢ E ×ˢ F)) hB hCDEF)
  -- Step 5: add `A`.
  have hABCDEF : P1 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := A) (B := (B ×ˢ C ×ˢ D ×ˢ E ×ˢ F)) hA hBCDEF)
  simpa using hABCDEF

theorem P3_prod_two_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : closure A = Set.univ) (hB : closure B = Set.univ) : P3 (A ×ˢ B) := by
  have hP3A : P3 (A : Set X) :=
    P3_of_dense (X := X) (A := A) hA
  have hP3B : P3 (B : Set Y) :=
    P3_of_dense (X := Y) (A := B) hB
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B)

theorem P2_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ A ⊆ interior (closure A) := by
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : closure (A : Set X) = A := hA.closure_eq
  constructor
  · -- `P2 A → A ⊆ interior (closure A)`
    intro hP2
    exact P3_of_P2 hP2
  · -- `A ⊆ interior (closure A) → P2 A`
    intro h_subset
    -- Rewrite the hypothesis using `closure A = A`.
    have h_subset' : (A : Set X) ⊆ interior A := by
      simpa [h_closure_eq] using h_subset
    -- Hence `A = interior A`, so `A` is open.
    have h_eq_int : (A : Set X) = interior A := by
      exact Set.Subset.antisymm h_subset' interior_subset
    have h_open : IsOpen (A : Set X) := by
      simpa [← h_eq_int] using (isOpen_interior : IsOpen (interior A))
    -- Open sets satisfy `P2`.
    exact P2_of_open (A := A) h_open

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ A ⊆ interior A := by
  have h_closure_eq : (closure (A : Set X)) = A := hA.closure_eq
  simpa [P3, h_closure_eq]

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ interior A = A := by
  -- First, rewrite `P3 A` in terms of an inclusion using the previous lemma.
  have h₁ : P3 A ↔ (A ⊆ interior A) := P3_closed_iff (A := A) hA
  -- For a closed set, this inclusion is equivalent to equality.
  have h₂ : (A ⊆ interior A) ↔ interior A = (A : Set X) := by
    constructor
    · intro hsub
      exact Set.Subset.antisymm interior_subset hsub
    · intro h_eq
      simpa [h_eq] using
        (subset_rfl : (interior A : Set X) ⊆ interior A)
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem P3_closed_complement : ∀ {X : Type*} [TopologicalSpace X] {A : Set X}, IsClosed A → P3 (Aᶜ) := by
  intro X _ A hA_closed
  have h_open : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact P3_of_open (A := Aᶜ) h_open

theorem P3_covering : ∀ {X : Type*} [TopologicalSpace X] {A : Set X} {ι : Sort*} {U : ι → Set X}, (∀ i, IsOpen (U i)) → (∀ i, A ⊆ U i) → (⋂ i, U i) ⊆ interior (closure A) → P3 A := by
  intro X _topX A ι U hUopen hAsub hInter x hxA
  have hxInter : x ∈ ⋂ i, U i := by
    apply Set.mem_iInter.2
    intro i
    exact hAsub i hxA
  exact hInter hxInter

theorem P2_homeomorph_iff : ∀ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X}, P2 A ↔ P2 (e '' A) := by
  intro X Y _ _ e A
  constructor
  · intro hA
    exact P2_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    -- Transport the property back along `e.symm`.
    have h : P2 (e.symm '' (e '' A)) :=
      P2_image_homeomorph (e := e.symm) (A := (e '' A)) hImg
    -- Identify the transported set with `A`.
    have hEq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h