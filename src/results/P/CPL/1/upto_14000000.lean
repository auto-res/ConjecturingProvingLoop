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


theorem P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have h_intA : interior A = A := hA.interior_eq
  have h_subset : (A : Set X) ⊆ interior (closure A) := by
    have h : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    simpa [h_intA] using h
  simpa [h_intA] using h_subset hx

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  exact
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
      (by simpa [hA.interior_eq] using hx)

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  intro x hx
  exact
    (interior_mono (closure_mono (interior_subset : interior A ⊆ A))) (h hx)

theorem closure_interior_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure (interior A) = closure A := by
  apply subset_antisymm
  · exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  ·
    have : closure A ⊆ closure (interior A) := by
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
      simpa [closure_closure] using h'
    simpa using this

theorem P2_iff_P1_for_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = (⊤ : Set X)) : P2 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    -- P2 ⇒ P1
    intro x hx
    exact interior_subset (hP2 hx)
  · intro hP1
    -- P1 ⇒ P2, using density
    intro x hx
    have h_closure : (closure (interior A) : Set X) = ⊤ := by
      have h_eq : closure (interior A) = closure A :=
        closure_interior_eq_of_P1 (A := A) hP1
      simpa [hA] using h_eq
    simpa [h_closure, interior_univ] using (by
      simp : x ∈ (⊤ : Set X))

theorem interior_eq_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P2 A) : interior A = A := by
  -- We prove both inclusions to establish equality.
  apply Set.Subset.antisymm
  · -- `interior A ⊆ A` is always true.
    exact interior_subset
  · -- For the reverse inclusion we use `h : A ⊆ interior (closure (interior A))`
    -- together with the fact that `closure (interior A) ⊆ A` when `A` is closed.
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    -- Since `A` is closed, `closure A = A`.
    have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
      have : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [hA.closure_eq] using this
    -- `interior` is monotone, so we can pass from the previous subset to interiors.
    have : interior (closure (interior A)) ⊆ interior A :=
      interior_mono h_closure_subset
    exact this hx'

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact
    (interior_subset :
      (interior (closure (interior A)) : Set X) ⊆ closure (interior A))
      (h hx)

theorem closure_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : closure A = interior (closure A) := by
  apply subset_antisymm
  ·
    intro x hx
    have hxA : x ∈ A := by
      simpa [hA.closure_eq] using hx
    exact h hxA
  ·
    exact interior_subset

theorem P1_closed_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 A ↔ closure (interior A) = A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    have h_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    simpa [hA.closure_eq] using h_eq
  · intro h_eq
    intro x hx
    simpa [h_eq] using hx

theorem P2_iff_P3_for_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P3_of_P2 (A := A) hP2
  · intro hP3
    intro x hxA
    -- First, `x` lies in the interior of `A`
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- Show that `interior A ⊆ interior (closure (interior A))`
    have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      have h_sub : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h_sub
      simpa [interior_interior] using h_mono
    exact h_subset hx_intA

theorem P1_iff_dense_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    exact closure_interior_eq_of_P1 (A := A) hP1
  · intro h_eq
    intro x hx
    have : (x ∈ closure A) := subset_closure hx
    simpa [h_eq] using this

theorem exists_closed_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, IsClosed B ∧ B ⊆ A ∧ P1 B := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset A, ?_⟩
  intro x hx
  cases hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure (interior A) = closure A := by
  simpa using closure_interior_eq_of_P1 (A := A) (P1_of_P2 (A := A) h)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        exact closure_mono h_int_subset
      exact h_subset hx_closureA
  | inr hxB =>
      -- `x ∈ B`
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have h_subset : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        exact closure_mono h_int_subset
      exact h_subset hx_closureB

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P2 (interior A) := by
  intro x hx
  -- First, see `x` as an element of `A` to make use of `h : P2 A`.
  have hxA : x ∈ (A : Set X) :=
    (interior_subset : (interior A : Set X) ⊆ A) hx
  -- Apply `h` to obtain membership in the desired interior.
  have h'x : x ∈ interior (closure (interior A)) := h hxA
  -- Rewrite the goal using `interior_interior`.
  simpa [interior_interior] using h'x

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- We show the required monotone inclusion.
      have h_subset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- First, `interior A ⊆ interior (A ∪ B)`.
        have h₁ : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have hA_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hA_sub
        -- Then, `closure (interior A) ⊆ closure (interior (A ∪ B))`.
        have h₂ : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        -- Finally, apply `interior_mono`.
        exact interior_mono h₂
      exact h_subset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      -- Again prove the required inclusion.
      have h_subset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `interior B ⊆ interior (A ∪ B)`.
        have h₁ : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have hB_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hB_sub
        -- `closure (interior B) ⊆ closure (interior (A ∪ B))`.
        have h₂ : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        -- Apply `interior_mono`.
        exact interior_mono h₂
      exact h_subset hxB'

theorem P1_Unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h i) hx_i
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, A j)) := by
    have h_int_subset :
        (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have hA_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hA_subset
    exact closure_mono h_int_subset
  exact h_subset hx_cl

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_i' : x ∈ interior (closure (interior (A i))) := (h i) hx_i
  have h_subset :
      (interior (closure (interior (A i))) : Set X) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- First, establish `interior (A i) ⊆ interior (⋃ j, A j)`.
    have h₁ : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have hA_i_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hA_i_subset
    -- Then, take closures and apply monotonicity again.
    have h₂ : (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, A j)) := closure_mono h₁
    -- Finally, pass to interiors.
    exact interior_mono h₂
  exact h_subset hx_i'

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ interior (closure A) := hA hxA
      -- We show the required inclusion.
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) := by
        -- First, `closure A ⊆ closure (A ∪ B)`.
        have h_closure : (closure A : Set X) ⊆ closure (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono h_sub
        -- Pass to interiors.
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ interior (closure B) := hB hxB
      -- Show the required inclusion for `B`.
      have h_subset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) := by
        -- `closure B ⊆ closure (A ∪ B)`.
        have h_closure : (closure B : Set X) ⊆ closure (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono h_sub
        -- Pass to interiors.
        exact interior_mono h_closure
      exact h_subset hxB'

theorem P3_Unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_i' : x ∈ interior (closure (A i)) := (h i) hx_i
  have h_subset :
      (interior (closure (A i)) : Set X) ⊆
        interior (closure (⋃ j, A j)) := by
    have h_closure :
        (closure (A i) : Set X) ⊆ closure (⋃ j, A j) := by
      have h_sub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_i'

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (interior A) := by
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P1 A) : P1 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Use the hypothesis `h` for the particular set `A`.
  have hx_cl : x ∈ closure (interior A) := (h A hA_mem) hxA
  -- Show that `closure (interior A)` is contained in the desired closure.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) := by
    -- First, `interior A ⊆ interior (⋃₀ 𝒜)`.
    have h_int_subset : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono h_sub
    -- Taking closures preserves the inclusion.
    exact closure_mono h_int_subset
  exact h_subset hx_cl

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P2 A) : P2 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Use the hypothesis for the particular set `A`.
  have hxA' : x ∈ interior (closure (interior A)) := (h A hA_mem) hxA
  -- Show the required inclusion between the interiors.
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- First, `interior A ⊆ interior (⋃₀ 𝒜)`.
    have h_int_subset : (interior A : Set X) ⊆ interior (⋃₀ 𝒜) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact interior_mono h_sub
    -- Taking closures preserves the inclusion.
    have h_closure_subset :
        (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_subset
    -- Finally, pass to interiors.
    exact interior_mono h_closure_subset
  exact h_subset hxA'

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxA' : x ∈ interior (closure A) := (h A hA_mem) hxA
  have h_subset :
      (interior (closure A) : Set X) ⊆
        interior (closure (⋃₀ 𝒜)) := by
    -- First, `closure A ⊆ closure (⋃₀ 𝒜)`.
    have h_closure : (closure A : Set X) ⊆ closure (⋃₀ 𝒜) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
      exact closure_mono h_sub
    -- Pass to interiors.
    exact interior_mono h_closure
  exact h_subset hxA'

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ interior A = A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact interior_eq_of_P2_closed (A := A) hA hP2
  · intro h_int_eq
    intro x hx
    simpa [h_int_eq, hA.closure_eq] using hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = (⊤ : Set X)) : P3 A := by
  intro x hx
  simpa [hA, interior_univ] using (by
    simp : x ∈ (⊤ : Set X))

theorem exists_P3_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P3 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P3_univ
  · simpa [closure_univ]

theorem P3_iff_nhds_within {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, interior (closure A) ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP3 x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    exact (isOpen_interior).mem_nhds hx_int
  · intro h x hx
    exact mem_of_mem_nhds (h x hx)

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P1 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P1_univ
  · simpa [closure_univ]

theorem P2_bunion {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B ∪ (A ∩ B)) := by
  -- First obtain `P2` for `A ∪ B`.
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Show that adding `A ∩ B` does not change the union.
  have h_eq : (A ∪ B ∪ (A ∩ B) : Set X) = A ∪ B := by
    -- Rewrite with associativity to apply `Set.union_eq_left`.
    have h_assoc : (A ∪ B ∪ (A ∩ B)) = (A ∪ B) ∪ (A ∩ B) := by
      simpa [Set.union_assoc]
    -- Since `A ∩ B ⊆ A ∪ B`, we can collapse the union.
    have h_sub : (A ∩ B : Set X) ⊆ A ∪ B := by
      intro x hx
      exact Or.inl hx.1
    have h_union : ((A ∪ B) ∪ (A ∩ B) : Set X) = A ∪ B :=
      (Set.union_eq_left).2 h_sub
    simpa [h_assoc] using h_union
  -- Prove the desired `P2` property.
  intro x hx
  -- Convert the hypothesis to membership in `A ∪ B`.
  have hxAB : x ∈ A ∪ B := by
    simpa [h_eq] using hx
  -- Apply `P2` for `A ∪ B`.
  have hx_int : x ∈ interior (closure (interior (A ∪ B))) := hAB hxAB
  -- Rewrite back to the required set using the equality.
  simpa [h_eq] using hx_int

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (closure A) := by
  intro x hx
  -- First, rewrite `closure (interior A)` using `P1 A`.
  have h_eq : (closure (interior A) : Set X) = closure A :=
    closure_interior_eq_of_P1 (A := A) h
  -- View `x` as an element of `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Show the required inclusion of closures.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
    have h_int :
        (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- Taking closures preserves the inclusion.
    exact closure_mono h_int
  exact h_subset hx'

theorem P1_iff_P2_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  refine ⟨fun _ => P2_of_isOpen (A := A) hA,
         fun _ => P1_of_isOpen (A := A) hA⟩

theorem P2_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P2` for `A ∪ B`
  have hAB : P2 (A ∪ B) :=
    P2_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P2` for `A ∪ B ∪ C`
  have hABC : P2 (A ∪ B ∪ C) := by
    have : P2 ((A ∪ B) ∪ C) :=
      P2_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P2` for `A ∪ B ∪ C ∪ D`
  have hABCD : P2 (A ∪ B ∪ C ∪ D) := by
    have : P2 ((A ∪ B ∪ C) ∪ D) :=
      P2_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD

theorem P2_sUnionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h

theorem P3_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P3` for `A ∪ B`
  have hAB : P3 (A ∪ B) :=
    P3_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P3` for `A ∪ B ∪ C`
  have hABC : P3 (A ∪ B ∪ C) := by
    have : P3 ((A ∪ B) ∪ C) :=
      P3_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P3` for `A ∪ B ∪ C ∪ D`
  have hABCD : P3 (A ∪ B ∪ C ∪ D) := by
    have : P3 ((A ∪ B ∪ C) ∪ D) :=
      P3_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  exact h (interior_subset hx)

theorem interior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : interior A = A := by
  -- First, deduce `interior (closure A) = A`.
  have h_int_closure : interior (closure A) = A := by
    have h_eq := closure_eq_of_P3_closed (A := A) hA h
    simpa [hA.closure_eq] using h_eq.symm
  -- Now obtain the desired equality.
  have : interior A = A := by
    calc
      interior A = interior (closure A) := by
        simpa [hA.closure_eq]
      _ = A := by
        simpa using h_int_closure
  exact this

theorem P1_and_P3_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : (P1 A ∧ P3 A) ↔ P2 A := by
  constructor
  · rintro ⟨hP1, hP3⟩
    intro x hx
    -- `x` is in the interior of `closure A` by `P3`.
    have hx_int_closureA : x ∈ interior (closure A) := hP3 hx
    -- From `P1` we have equality of the two closures.
    have h_closure_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Rewrite to obtain the desired membership.
    simpa [h_closure_eq] using hx_int_closureA
  · intro hP2
    exact ⟨P1_of_P2 (A := A) hP2, P3_of_P2 (A := A) hP2⟩

theorem P2_iff_nhds {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, interior (closure (interior A)) ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP2 x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    exact (isOpen_interior).mem_nhds hx_int
  · intro h x hx
    have h_mem : interior (closure (interior A)) ∈ 𝓝 x := h x hx
    exact mem_of_mem_nhds h_mem

theorem P2_of_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := (P1_and_P3_iff_P2 (A := A)).1 ⟨h1, h3⟩

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : P3 A := by
  intro x hx
  exact h (subset_closure hx)

theorem exists_P2_between {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : ∃ B : Set X, A ⊆ B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), ?_, P2_univ⟩
  ·
    intro x hx
    simp

theorem P3_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior A) : P3 A := by
  intro x hx
  have hx_intA : x ∈ interior A := by
    have : x ∈ closure A := subset_closure hx
    simpa [h] using this
  simpa [h, interior_interior] using hx_intA

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Hence `e x` lies in `closure (e '' interior A)`
  have hx_closure_img : (e x) ∈ closure (e '' interior A : Set Y) := by
    -- First view it as an element of `e '' closure (interior A)`
    have h_mem : (e x) ∈ (e '' closure (interior A) : Set Y) :=
      ⟨x, hx_cl, rfl⟩
    -- Rewrite using `image_closure`
    simpa [e.image_closure (s := interior A)] using h_mem
  -- `e '' interior A` is exactly `interior (e '' A)`
  have h_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  -- Conclude the desired membership
  simpa [h_eq] using hx_closure_img

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  -- Start with a point `(x, y)` belonging to `A ×ˢ B`.
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P2` on each coordinate.
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  have hy : y ∈ interior (closure (interior B)) := hB hyB

  -- Define an auxiliary open rectangle around `(x, y)`.
  let U : Set (X × Y) :=
    Set.prod (interior (closure (interior A)))
             (interior (closure (interior B)))

  -- `U` is open.
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior : IsOpen (interior (closure (interior A)))).prod
      (isOpen_interior : IsOpen (interior (closure (interior B))))

  -- Show `U ⊆ closure (interior (A ×ˢ B))`.
  have hU_subset_closure :
      (U : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases q with ⟨u, v⟩
    dsimp [U] at hq
    rcases hq with ⟨hu, hv⟩
    -- Coordinates lie in the corresponding closures.
    have hu_cl : u ∈ closure (interior A) := interior_subset hu
    have hv_cl : v ∈ closure (interior B) := interior_subset hv
    -- A useful identification of closures of products.
    have h_cl_eq :
        (closure (Set.prod (interior A) (interior B)) :
            Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    -- Hence `(u, v)` is in the closure of the product of interiors.
    have h_mem_cl :
        ((u, v) : X × Y) ∈
          closure (Set.prod (interior A) (interior B)) := by
      have : ((u, v) : X × Y) ∈
          Set.prod (closure (interior A)) (closure (interior B)) :=
        ⟨hu_cl, hv_cl⟩
      simpa [h_cl_eq] using this
    -- The product of interiors is inside the interior of the product.
    have h_subset_prod_int :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- First inclusion into `A ×ˢ B`.
      have h_sub :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
            Set.prod A B :=
        Set.prod_mono interior_subset interior_subset
      -- Openness of the product of interiors.
      have h_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior : IsOpen (interior A)).prod
          (isOpen_interior : IsOpen (interior B))
      exact interior_maximal h_sub h_open
    -- Pass to closures.
    have h_closure_subset :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_subset_prod_int
    exact h_closure_subset h_mem_cl

  -- From the two previous facts,
  -- `U ⊆ interior (closure (interior (A ×ˢ B)))`.
  have hU_subset_int :
      (U : Set (X × Y)) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal hU_subset_closure hU_open

  -- `(x, y)` belongs to `U`, hence to the desired interior set.
  have hxyU : ((x, y) : X × Y) ∈ U := by
    dsimp [U]
    exact ⟨hx, hy⟩

  exact hU_subset_int hxyU

theorem P2_dense_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) = (⊤ : Set X) → P2 A := by
  intro h_dense
  -- From `P1 A` we know the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    closure_interior_eq_of_P1 (A := A) hA
  -- Hence `closure A` is also the whole space.
  have h_closureA_univ : closure A = (⊤ : Set X) := by
    simpa [h_eq] using h_dense
  -- Use the equivalence for dense sets to obtain `P2 A`.
  exact (P2_iff_P1_for_dense (A := A) h_closureA_univ).2 hA

theorem exists_P1_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ B, B ⊆ A ∧ P1 B := by
  exact ⟨A, ⟨subset_rfl, P1_of_P2 (A := A) hA⟩⟩

theorem P1_of_nhds {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, interior A ∈ 𝓝 x) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have h_mem : interior A ∈ 𝓝 x := h x hx
    exact mem_of_mem_nhds h_mem
  exact subset_closure hx_int

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P3` on each coordinate.
  have hx : x ∈ interior (closure A) := hA hxA
  have hy : y ∈ interior (closure B) := hB hyB
  -- Define an auxiliary open rectangle around `(x, y)`.
  let U : Set (X × Y) :=
    Set.prod (interior (closure A)) (interior (closure B))
  -- `U` is open.
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior : IsOpen (interior (closure A))).prod
      (isOpen_interior : IsOpen (interior (closure B)))
  -- Show `U ⊆ closure (A ×ˢ B)`.
  have hU_subset_closure :
      (U : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases q with ⟨u, v⟩
    dsimp [U] at hq
    rcases hq with ⟨hu, hv⟩
    -- Coordinates lie in the corresponding closures.
    have hu_cl : u ∈ closure A := interior_subset hu
    have hv_cl : v ∈ closure B := interior_subset hv
    -- Identify the closure of the product.
    have h_cl_eq :
        (closure (Set.prod A B) : Set (X × Y)) =
          Set.prod (closure A) (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) =
            Set.prod (closure A) (closure B))
    -- Conclude membership.
    have h_mem : ((u, v) : X × Y) ∈ Set.prod (closure A) (closure B) :=
      ⟨hu_cl, hv_cl⟩
    simpa [h_cl_eq] using h_mem
  -- From the two previous facts,
  -- `U ⊆ interior (closure (A ×ˢ B))`.
  have hU_subset_int :
      (U : Set (X × Y)) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal hU_subset_closure hU_open
  -- `(x, y)` belongs to `U`, hence to the desired interior set.
  have hxyU : ((x, y) : X × Y) ∈ U := by
    dsimp [U]
    exact ⟨hx, hy⟩
  exact hU_subset_int hxyU

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (⊤ : Set X)) : P2 A := by
  intro x hx
  simpa [h, interior_univ]

theorem P3_closed_iff_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ interior A = closure A := by
  refine ⟨?forward, ?backward⟩
  · intro hP3
    -- From `P3` and closedness we get `interior A = A`.
    have h_int_eq_A : interior A = A :=
      interior_eq_of_P3_closed (A := A) hA hP3
    -- Replace `A` by `closure A` (which equals `A` because `A` is closed).
    have h_int_eq_cl : interior A = closure A := by
      calc
        interior A = A := h_int_eq_A
        _ = closure A := (hA.closure_eq).symm
    exact h_int_eq_cl
  · intro h_int_eq_cl
    -- Turn the given equality around to fit `P3_of_closure_eq_interior`.
    have h_cl_eq_int : closure A = interior A := h_int_eq_cl.symm
    exact P3_of_closure_eq_interior (A := A) h_cl_eq_int

theorem exists_closed_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, IsClosed B ∧ B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P2_empty⟩

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- `x` and `y` lie in the respective closures of the interiors.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- Hence `(x, y)` lies in the closure of the product of interiors.
  have h_mem_cl :
      ((x, y) : X × Y) ∈
        closure (Set.prod (interior A) (interior B)) := by
    -- Identify the closure explicitly.
    have h_eq :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    -- Membership follows from the coordinate facts.
    have : ((x, y) : X × Y) ∈
        Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hx_cl, hy_cl⟩
    simpa [h_eq] using this
  -- The closure of the product of interiors is contained in the desired closure.
  have h_subset :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
        closure (interior (Set.prod A B)) := by
    -- First, the product of interiors sits inside the interior of the product.
    have h_sub :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- `interior A ×ˢ interior B ⊆ A ×ˢ B`.
      have h₁ :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
            Set.prod A B :=
        Set.prod_mono interior_subset interior_subset
      -- The product of interiors is open.
      have h_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior : IsOpen (interior A)).prod
          (isOpen_interior : IsOpen (interior B))
      -- Apply `interior_maximal`.
      exact interior_maximal h₁ h_open
    -- Pass to closures.
    exact closure_mono h_sub
  exact h_subset h_mem_cl

theorem P3_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P1 A := by
  refine ⟨fun _ => P1_of_isOpen (A := A) hA,
         fun _ => P3_of_isOpen (A := A) hA⟩

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P2 A) : P2 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` belongs to the interior of `closure (interior A)`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Move the membership through the homeomorphism `e`
  have h1 : (e x) ∈ interior (e '' closure (interior A) : Set Y) := by
    -- first see it in the image of the interior
    have h_mem : (e x) ∈ (e '' interior (closure (interior A)) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    simpa [e.image_interior (s := closure (interior A))] using h_mem
  -- Rewrite the image of the closure via `e.image_closure`
  have h2 : (e x) ∈ interior (closure (e '' interior A : Set Y)) := by
    simpa [e.image_closure (s := interior A)] using h1
  -- Replace `e '' interior A` with `interior (e '' A)`
  have h_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  have h3 : (e x) ∈ interior (closure (interior (e '' A))) := by
    simpa [h_eq] using h2
  exact h3

theorem exists_P2_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P2 A ∧ closure A = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P2_univ
  · simpa [closure_univ]

theorem P3_iff_P2_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa using
    (P3_iff_P1_for_open (A := A) hA).trans
      (P1_iff_P2_for_open (A := A) hA)

theorem P1_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = (⊤ : Set X)) : P1 A := by
  intro x hx
  simpa [h] using (by
    simp : x ∈ (⊤ : Set X))

theorem P3_of_dense_int_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = (⊤ : Set X)) : P3 A := by
  intro x hx
  have : (x : X) ∈ (⊤ : Set X) := by
    simp
  simpa [h] using this

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P1 (closure A) := by
  intro x hx
  have h_subset : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    exact closure_mono (hA : (A : Set X) ⊆ interior (closure A))
  exact h_subset hx

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : P3 (interior A) := by
  intro x hx
  -- use the hypothesis `h` to avoid an unused-argument warning
  have _ := h
  -- `interior A` is open and contained in its own closure,
  -- hence it is contained in the interior of that closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have h_open : IsOpen (interior A) := isOpen_interior
    exact
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        h_open
  exact h_subset hx

theorem P1_prod_of_P2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P1 (Set.prod A B) := by
  -- First, obtain `P2` for the product using the hypotheses.
  have h : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  -- Then convert `P2` to `P1`.
  exact P1_of_P2 (A := Set.prod A B) h

theorem P2_union_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ (A ∩ B)) := by
  -- Use `hB` to avoid an unused variable warning
  have _ := hB
  -- Since `A ∩ B ⊆ A`, the union collapses to `A`.
  have h_eq : (A ∪ (A ∩ B) : Set X) = A := by
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro x hx
      exact hx.1
    simpa using (Set.union_eq_left.2 h_subset)
  simpa [h_eq] using hA

theorem P1_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P1_univ (X := X))

theorem P1_iff_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ frontier A ⊆ closure (interior A) := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    -- From `P1` we have equality of the two closures.
    have h_eq : closure (interior A) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Show that the frontier is contained in `closure (interior A)`.
    intro x hx
    -- `hx.1 : x ∈ closure A`.
    have hx_cl : (x : X) ∈ closure A := hx.1
    simpa [h_eq] using hx_cl
  · intro hFront
    -- We prove `P1 A`.
    intro x hxA
    by_cases h_int : x ∈ interior A
    · -- If `x` is interior, the result is immediate.
      exact subset_closure h_int
    · -- Otherwise, `x` lies on the frontier.
      have hx_cl : (x : X) ∈ closure A := subset_closure hxA
      have hx_front : x ∈ frontier A := ⟨hx_cl, h_int⟩
      exact hFront hx_front

theorem P1_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : interior (closure (interior A)) = interior (closure A) := by
  simpa [closure_interior_eq_of_P1 (A := A) h]

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : closure A = (⊤ : Set X)) : P1 A := by
  intro x hx
  -- Since `A` is closed and dense, it is the whole space.
  have hA_univ : (A : Set X) = (⊤ : Set X) := by
    calc
      (A : Set X) = closure A := by
        simpa using (hA.closure_eq).symm
      _ = (⊤ : Set X) := by
        simpa using hd
  -- The desired inclusion is now immediate.
  simpa [hA_univ, interior_univ, closure_univ]

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : closure A = (⊤ : Set X)) : P2 A := by
  intro x hx
  -- Since `A` is closed and dense, it is the whole space.
  have hA_univ : (A : Set X) = (⊤ : Set X) := by
    calc
      (A : Set X) = closure A := (hA.closure_eq).symm
      _ = (⊤ : Set X) := hd
  -- Rewrite `hx` using this fact.
  have hx_univ : (x : X) ∈ (⊤ : Set X) := by
    simpa [hA_univ] using hx
  -- The required interior set is also the whole space.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod A (Set.prod B C)) := by
  -- First derive `P1` for the product `B × C`.
  have hBC : P1 (Set.prod B C) := P1_prod (A := B) (B := C) hB hC
  -- Then apply `P1_prod` once more to get the desired result.
  exact P1_prod (A := A) (B := Set.prod B C) hA hBC

theorem P3_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P3_univ (X := X))

theorem P2_of_frontier_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P2 A := by
  classical
  -- Step 1: prove `closure A ⊆ interior A`.
  have h_cl_sub : (closure A : Set X) ⊆ interior A := by
    intro x hx_cl
    by_cases hx_int : x ∈ interior A
    · exact hx_int
    ·
      -- Then `x` lies in the frontier, which is empty.
      have hx_front : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        change x ∈ closure A \ interior A
        exact And.intro hx_cl hx_int
      have : x ∈ (∅ : Set X) := by
        simpa [h] using hx_front
      cases this
  -- Step 2: deduce `A ⊆ interior A`.
  have hA_sub_int : (A : Set X) ⊆ interior A := by
    intro x hxA
    exact h_cl_sub (subset_closure hxA)
  -- Step 3: hence `interior A = A`, so `A` is open.
  have h_int_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hA_sub_int
  have hA_open : IsOpen A := by
    simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
  -- Step 4: apply the open-set lemma to obtain `P2 A`.
  exact P2_of_isOpen (A := A) hA_open

theorem P3_of_frontier_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P3 A := by
  classical
  intro x hxA
  -- First, show that `closure A ⊆ interior A`.
  have h_cl_sub_int : (closure A : Set X) ⊆ interior A := by
    intro y hy_cl
    by_cases hy_int : y ∈ interior A
    · exact hy_int
    ·
      -- Otherwise, `y` is on the frontier, which is empty.
      have hy_front : y ∈ frontier A := by
        change y ∈ (closure A \ interior A : Set X)
        exact ⟨hy_cl, hy_int⟩
      have : y ∈ (∅ : Set X) := by
        simpa [h] using hy_front
      cases this
  -- Hence `A ⊆ interior A`.
  have hA_sub_int : (A : Set X) ⊆ interior A := fun y hyA =>
    h_cl_sub_int (subset_closure hyA)
  -- Therefore `x ∈ interior A`.
  have hx_intA : x ∈ interior A := hA_sub_int hxA
  -- Finally, `interior A ⊆ interior (closure A)`.
  have h_int_subset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_int_subset hx_intA

theorem P3_of_interior_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = (⊤ : Set X)) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have : (x : X) ∈ (⊤ : Set X) := by
      simp
    simpa [h] using this
  exact
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int

theorem P1_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) : P1 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P1` for `A ∪ B`
  have hAB : P1 (A ∪ B) :=
    P1_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P1` for `A ∪ B ∪ C`
  have hABC : P1 (A ∪ B ∪ C) := by
    have : P1 ((A ∪ B) ∪ C) :=
      P1_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P1` for `A ∪ B ∪ C ∪ D`
  have hABCD : P1 (A ∪ B ∪ C ∪ D) := by
    have : P1 ((A ∪ B ∪ C) ∪ D) :=
      P1_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of `closure A`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Transport through the homeomorphism
  have h1 : (e x) ∈ interior (e '' closure A : Set Y) := by
    -- first as an element of `e '' interior (closure A)`
    have hmem : (e x) ∈ (e '' interior (closure A) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    simpa [e.image_interior (s := closure A)] using hmem
  -- Rewrite the image of the closure
  have h2 : (e x) ∈ interior (closure (e '' A : Set Y)) := by
    simpa [e.image_closure (s := A)] using h1
  exact h2

theorem P2_sigma {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.prod A (Set.prod B C)) := by
  -- First derive `P3` for the product `B × C`.
  have hBC : P3 (Set.prod B C) := P3_prod (A := B) (B := C) hB hC
  -- Then apply `P3_prod` once more to get the desired result.
  exact P3_prod (A := A) (B := Set.prod B C) hA hBC

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  -- Step 1: obtain `P3` for `A ∪ B`.
  have hAB : P3 (A ∪ B) :=
    P3_union (A := A) (B := B) hA hB
  -- Step 2: combine with `C`.
  have hABC : P3 ((A ∪ B) ∪ C) :=
    P3_union (A := (A ∪ B)) (B := C) hAB hC
  -- Reassociate unions to match the goal.
  simpa [Set.union_assoc] using hABC

theorem exists_compact_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty⟩

theorem exists_P3_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ B : Set X, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P3_empty⟩

theorem exists_open_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, (Set.subset_univ A), P3_univ (X := X)⟩

theorem P1_empty_iff {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P1_empty (X := X)

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_univ (X := X)

theorem P3_iff_nhds_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, closure A ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP3 x hx
    -- From `P3` we know that `x ∈ interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hx
    -- The interior is open, hence a neighbourhood of `x`.
    have h_nhds_int : (interior (closure A) : Set X) ∈ 𝓝 x :=
      (isOpen_interior : IsOpen (interior (closure A))).mem_nhds hx_int
    -- Any superset of a neighbourhood is again a neighbourhood.
    exact Filter.mem_of_superset h_nhds_int interior_subset
  · intro h x hx
    -- We are given that `closure A` is a neighbourhood of `x`.
    have h_nhds_cl : (closure A : Set X) ∈ 𝓝 x := h x hx
    -- Unpack the neighbourhood condition to obtain an open set `U`
    -- with `x ∈ U ⊆ closure A`.
    rcases mem_nhds_iff.1 h_nhds_cl with ⟨U, hU_sub, hU_open, hxU⟩
    -- Since `U` is open and contained in `closure A`, it is contained
    -- in `interior (closure A)`.
    have hU_int : (U : Set X) ⊆ interior (closure A) :=
      interior_maximal hU_sub hU_open
    -- Therefore `x ∈ interior (closure A)`.
    exact hU_int hxU

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P2 (Set.prod A B)) : P2 (Set.prod B A) := by
  -- Let `e` be the coordinate-swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)

  -- Transport `P2` along `e`.
  have h_image : P2 (e '' (Set.prod A B)) :=
    P2_image_homeomorph (e := e) (A := Set.prod A B) h

  -- Identify the image of `A ×ˢ B` under `e`.
  have h_eq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · -- `→`
      rintro ⟨q, hq, rfl⟩
      rcases q with ⟨a, b⟩
      rcases hq with ⟨ha, hb⟩
      -- After swapping we are at `(b, a)`.
      simpa [e] using And.intro hb ha
    · -- `←`
      intro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, ?_⟩
      · simpa using And.intro ha hb
      · simp [e]

  -- Prove `P2` for `B ×ˢ A`.
  intro p hp
  -- Regard `p` as an element of the image set.
  have hp_image : p ∈ (e '' (Set.prod A B)) := by
    simpa [h_eq] using hp
  -- Apply the transported `P2` and rewrite back using `h_eq`.
  have hp_int := h_image hp_image
  simpa [h_eq] using hp_int

theorem P3_sigma_subtype {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 {x : X | ∃ i, x ∈ A i} := by
  -- First obtain `P3` for the union `⋃ i, A i`.
  have hP3_union : P3 (⋃ i, A i) := P3_Unionᵢ (A := A) h
  -- Show that the set of elements belonging to some `A i` coincides with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
  -- Transfer `P3` along the above equality.
  intro x hx
  -- View `x` as an element of the union.
  have hx_union : (x : X) ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P3` for the union.
  have hx_int : (x : X) ∈ interior (closure (⋃ i, A i)) :=
    hP3_union hx_union
  -- Rewrite back using the equality.
  simpa [h_eq] using hx_int

theorem P3_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P3 (A ∪ interior A) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_int_clA : x ∈ interior (closure A) := hA hxA
      -- `closure A ⊆ closure (A ∪ interior A)`
      have h_closure :
          (closure A : Set X) ⊆ closure (A ∪ interior A) := by
        have h_sub : (A : Set X) ⊆ A ∪ interior A := by
          intro y hy
          exact Or.inl hy
        exact closure_mono h_sub
      -- hence the desired inclusion on interiors
      have h_subset :
          (interior (closure A) : Set X) ⊆
            interior (closure (A ∪ interior A)) :=
        interior_mono h_closure
      exact h_subset hx_int_clA
  | inr hx_intA =>
      -- `x ∈ interior A`
      -- First view `x` as an element of `A`.
      have hxA : x ∈ A := interior_subset hx_intA
      -- Apply `P3` for `A`.
      have hx_int_clA : x ∈ interior (closure A) := hA hxA
      -- `closure A ⊆ closure (A ∪ interior A)`
      have h_closure :
          (closure A : Set X) ⊆ closure (A ∪ interior A) := by
        have h_sub : (A : Set X) ⊆ A ∪ interior A := by
          intro y hy
          exact Or.inl hy
        exact closure_mono h_sub
      -- hence the desired inclusion on interiors
      have h_subset :
          (interior (closure A) : Set X) ⊆
            interior (closure (A ∪ interior A)) :=
        interior_mono h_closure
      exact h_subset hx_int_clA

theorem P2_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A ⊆ interior (closure (interior A))) : P2 A := by
  intro x hxA
  by_cases hx_intA : x ∈ interior A
  · -- `x` already lies in the interior of `A`
    -- and hence in the required interior set.
    have h_subset :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      -- `interior A` is open and contained in `closure (interior A)`.
      have h_open : IsOpen (interior A) := isOpen_interior
      exact
        interior_maximal
          (subset_closure :
            (interior A : Set X) ⊆ closure (interior A))
          h_open
    exact h_subset hx_intA
  · -- `x` is **not** in the interior of `A`, hence on the frontier.
    have hx_frontier : x ∈ frontier A := by
      -- `frontier A = closure A \ interior A`.
      change x ∈ closure A \ interior A
      refine And.intro (subset_closure hxA) ?_
      exact hx_intA
    exact h hx_frontier

theorem P2_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P2 A := by
  intro x hx
  -- Since `X` has at most one element, a non-empty subset is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Trivial membership in `univ`.
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite the goal using `hA_univ`.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ

theorem P3_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P3 A := by
  intro x hx
  classical
  -- In a subsingleton space, any non-empty subset is the whole space.
  have A_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; 
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence `interior (closure A)` is the whole space, so the goal is immediate.
  have : (x : X) ∈ interior (closure A) := by
    have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [A_univ, closure_univ, interior_univ] using hx_univ
  exact this

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) {f : X → Y} (hf : Continuous f) (hU2 : P2 U) : P2 (f ⁻¹' U) := by
  -- use `hU2` to avoid unused argument warning
  have _ := hU2
  -- the preimage of an open set under a continuous map is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- any open set satisfies `P2`
  exact P2_of_isOpen (A := f ⁻¹' U) h_open

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 (closure A)) : P3 A := by
  intro x hxA
  -- `x` lies in the closure of `A`.
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  -- Apply `P2` for `closure A`.
  have hx_int :
      x ∈ interior (closure (interior (closure A))) := h hx_cl
  -- Show the interior set above is contained in `interior (closure A)`.
  have h_subset :
      (interior (closure (interior (closure A))) : Set X) ⊆
        interior (closure A) := by
    -- First, prove an inclusion for the closures.
    have h_closure_sub :
        (closure (interior (closure A)) : Set X) ⊆ closure A := by
      -- Since `interior (closure A) ⊆ closure A`, take closures.
      have h' : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      have h'' :
          (closure (interior (closure A)) : Set X) ⊆
            closure (closure A) :=
        closure_mono h'
      simpa [closure_closure] using h''
    -- Pass to interiors.
    exact interior_mono h_closure_sub
  -- Conclude the desired membership.
  exact h_subset hx_int

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod A (Set.prod B C)) := by
  -- First derive `P2` for the product `B × C`.
  have hBC : P2 (Set.prod B C) := P2_prod (A := B) (B := C) hB hC
  -- Then apply `P2_prod` once more to get the desired result.
  exact P2_prod (A := A) (B := Set.prod B C) hA hBC

theorem P3_preimage_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : IsClosed B) {f : X → Y} (hf : Continuous f) (hB3 : P3 B) : P3 (f ⁻¹' B) := by
  intro x hx
  -- `B` is open because it is closed and satisfies `P3`.
  have h_int_eq : interior B = B :=
    interior_eq_of_P3_closed (A := B) hB hB3
  -- Regard `x` as belonging to the preimage of `interior B`.
  have hx_pre : x ∈ f ⁻¹' interior B := by
    simpa [Set.preimage, h_int_eq] using hx
  -- The preimage of `interior B` is open.
  have h_open : IsOpen (f ⁻¹' interior B) :=
    (isOpen_interior : IsOpen (interior B)).preimage hf
  -- This set is contained in the preimage of `B`.
  have h_sub : (f ⁻¹' interior B : Set X) ⊆ f ⁻¹' B :=
    Set.preimage_mono (interior_subset : (interior B : Set Y) ⊆ B)
  -- Hence it is contained in the interior of the preimage of `B`.
  have h_sub_int :
      (f ⁻¹' interior B : Set X) ⊆ interior (f ⁻¹' B) :=
    interior_maximal h_sub h_open
  -- Therefore `x` lies in `interior (f ⁻¹' B)`.
  have hx_int : x ∈ interior (f ⁻¹' B) := h_sub_int hx_pre
  -- Finally, use monotonicity of `interior` with respect to `closure`.
  exact
    (interior_mono
        (subset_closure : (f ⁻¹' B : Set X) ⊆ closure (f ⁻¹' B))) hx_int

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) {f : X → Y} (hf : Continuous f) (hU3 : P3 U) : P3 (f ⁻¹' U) := by
  -- use `hU3` to avoid an unused-argument warning
  have _ := hU3
  -- the preimage of an open set under a continuous map is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- any open set satisfies `P3`
  exact P3_of_isOpen (A := f ⁻¹' U) h_open

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (A ∪ interior A) := by
  exact P1_union (A := A) (B := interior A) hA (P1_interior (A := A) hA)

theorem P1_prod_swap {X : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P1 (Set.prod A B)) : P1 (Set.prod B A) := by
  -- Define the coordinate-swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P1` along `e`.
  have h_image : P1 (e '' (Set.prod A B)) :=
    P1_image_homeomorph (e := e) (A := Set.prod A B) h
  -- Identify the image of `A ×ˢ B` under `e`.
  have h_eq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨a, b⟩
      rcases hq with ⟨ha, hb⟩
      simpa using And.intro hb ha
    · intro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro ha hb
      · simp [e]
  -- Re-express `h_image` using the above identification.
  simpa [P1, h_eq] using h_image

theorem P2_Union_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  simpa using P2_unionᵢ (A := A) h

theorem P1_Union_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : Continuous f) (hA : P1 A) : P1 (⋃ y, f ⁻¹' {y}) := by
  -- use the assumptions to avoid unused-variable warnings
  have _ := hf
  have _ := hA
  -- identify the union as the whole space
  have h_eq : (⋃ y, f ⁻¹' ({y} : Set Y)) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; simp
    · intro _; exact Set.mem_iUnion.2 ⟨f x, by simp⟩
  simpa [h_eq] using (P1_univ (X := X))

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P3 (Set.prod A B)) : P3 (Set.prod B A) := by
  -- Define the coordinate‐swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P3` along `e`.
  have h_image : P3 (e '' (Set.prod A B)) :=
    P3_image_homeomorph (e := e) (A := Set.prod A B) h
  -- Identify the image of `A ×ˢ B` under `e`.
  have h_eq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨a, b⟩
      rcases hq with ⟨ha, hb⟩
      simpa using And.intro hb ha
    · intro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro ha hb
      · simp [e]
  -- Now prove `P3` for `B ×ˢ A`.
  intro p hp
  -- Regard `p` as an element of the image set.
  have hp_image : p ∈ (e '' (Set.prod A B)) := by
    simpa [h_eq] using hp
  -- Apply `P3` for the image.
  have hp_int := h_image hp_image
  -- Rewrite back to the desired set.
  simpa [h_eq] using hp_int

theorem P1_sigma_subtype {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 {x : X | ∃ i, x ∈ A i} := by
  -- First, obtain `P1` for the union `⋃ i, A i`.
  have hP1_union : P1 (⋃ i, A i) := P1_Unionᵢ (A := A) h
  -- Identify the σ-type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hx⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      exact ⟨i, hx⟩
  -- Now establish `P1` for the σ-type set.
  intro x hx
  -- Regard `x` as an element of the union.
  have hx_union : (x : X) ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P1` for the union.
  have hx_cl : x ∈ closure (interior (⋃ i, A i)) := hP1_union hx_union
  -- Rewrite using the equality of sets.
  simpa [h_eq] using hx_cl

theorem P2_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, IsClosed A ∧ P2 A) : P2 (⋃₀ 𝒜) := by
  exact P2_sUnion (fun A hA => (h𝒜 A hA).2)

theorem P3_dense_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = (⊤ : Set X)) : P3 A := by
  exact P3_of_P2 (A := A) (P2_of_dense_interior (A := A) hd)

theorem exists_P1_dense_open {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P1 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P1_univ (X := X)
  · simpa [closure_univ]

theorem exists_P3_open_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P3 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P3_univ (X := X)
  · simpa [closure_univ]

theorem P3_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : frontier A ⊆ interior (closure A)) : P3 A := by
  intro x hxA
  by_cases h_int : x ∈ interior A
  ·
    -- `x` already lies in `interior A`, hence in `interior (closure A)`
    have h_subset :
        (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact h_subset h_int
  ·
    -- Otherwise, `x` is on the frontier of `A`
    have hx_frontier : x ∈ frontier A := by
      have hx_cl : (x : X) ∈ closure A := subset_closure hxA
      exact ⟨hx_cl, h_int⟩
    -- Apply the hypothesis on the frontier
    exact h hx_frontier

theorem exists_P2_open_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ P2 U ∧ closure U = (⊤ : Set X) := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact P2_univ (X := X)
  · simpa [closure_univ]

theorem exists_P1_P2_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, P1 A ∧ P2 A ∧ P3 A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  exact ⟨P1_univ (X := X), P2_univ (X := X), P3_univ (X := X)⟩

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) : P1 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- Obtain `P1` for the product `B × (C × D)`.
  have hBCD : P1 (Set.prod B (Set.prod C D)) :=
    P1_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P1_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- Obtain `P2` for the product `B × (C × D)`.
  have hBCD : P2 (Set.prod B (Set.prod C D)) :=
    P2_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P2_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (Set.prod A (Set.prod B (Set.prod C D))) := by
  -- First, obtain `P3` for the product `B × (C × D)`.
  have hBCD : P3 (Set.prod B (Set.prod C D)) :=
    P3_prod_three (A := B) (B := C) (C := D) hB hC hD
  -- Combine with `A` to get the desired result.
  exact P3_prod (A := A) (B := Set.prod B (Set.prod C D)) hA hBCD

theorem P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : P3 A) : P1 A := by
  intro x hx
  -- From `P3`, `x` lies in the interior of `closure A`, which equals `interior A`
  -- because `A` is closed.
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := h hx
    simpa [hA.closure_eq] using this
  -- The closure of `interior A` contains `x`.
  exact subset_closure hx_int

theorem P1_of_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 (interior A) := by
  -- First, obtain `P2` for `interior A` from the given hypothesis.
  have hP2 : P2 (interior A) := P2_interior (A := A) h
  -- Convert this `P2` statement to `P1`.
  exact P1_of_P2 (A := interior A) hP2

theorem P2_Union_homeomorph_fibers {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : P2 (⋃ y, e ⁻¹' {y}) := by
  -- The union of all fibres of `e` is the whole space.
  have h_eq : (⋃ y : Y, e ⁻¹' ({y} : Set Y)) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; simp
    · intro _; 
      have hx : x ∈ e ⁻¹' ({e x} : Set Y) := by
        simp
      exact Set.mem_iUnion.2 ⟨e x, hx⟩
  -- Conclude using the fact that `P2` holds for `Set.univ`.
  simpa [h_eq] using (P2_univ (X := X))

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using (P1_iff_dense_inter_interior (A := A))

theorem P1_comap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : P1 B) : P1 (e ⁻¹' B) := by
  -- Transport `P1 B` along the inverse homeomorphism `e.symm`.
  have hImage : P1 (e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  -- The image of `B` under `e.symm` coincides with the pre-image of `B` under `e`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      refine ⟨e x, hx, ?_⟩
      simpa using e.symm_apply_apply x
  -- Rewrite the obtained `P1` statement using this equality.
  simpa [h_eq] using hImage

theorem P2_sigma_of_isClosed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) (h : ∀ i, P2 (A i)) : P2 {x : X | ∃ i, x ∈ A i} := by
  -- Use `hA` to avoid an unused-argument warning
  have _ := hA
  -- Obtain `P2` for the union `⋃ i, A i`.
  have hP2_union : P2 (⋃ i, A i) := P2_unionᵢ (A := A) h
  -- Identify the σ–type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hx⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      exact ⟨i, hx⟩
  -- Transfer the `P2` property along the equality.
  intro x hx
  -- Regard `x` as an element of the union.
  have hx_union : x ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P2` for the union.
  have hx_int : x ∈ interior (closure (interior (⋃ i, A i))) :=
    hP2_union hx_union
  -- Rewrite back using the equality.
  simpa [h_eq] using hx_int

theorem P1_pow_two {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (A ×ˢ A) := by
  simpa using (P1_prod (A := A) (B := A) hA hA)

theorem P1_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, IsClosed A ∧ P1 A) : P1 (⋃₀ 𝒜) := by
  exact P1_sUnion (𝒜 := 𝒜) (fun A hA => (h A hA).2)

theorem P3_Union_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  exact P3_of_isOpen (A := interior (closure (A : Set X))) isOpen_interior

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior (closure A)))) := by
  exact
    P2_of_isOpen
      (A := interior (closure (interior (closure A))))
      isOpen_interior

theorem P2_sigma_type {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 {x : X | ∃ i, x ∈ A i} := by
  -- First, obtain `P2` for the union `⋃ i, A i`.
  have hP2_union : P2 (⋃ i, A i) := P2_unionᵢ (A := A) h
  -- Identify the σ–type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
  -- Transfer the `P2` property along the equality.
  intro x hx
  have hx_union : x ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  have hx_int : x ∈ interior (closure (interior (⋃ i, A i))) :=
    hP2_union hx_union
  simpa [h_eq] using hx_int

theorem P1_prod_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.image (fun p : X × Y => (p.1, p.2)) (Set.prod A B)) := by
  -- The map `p ↦ (p.1, p.2)` is the identity, hence its image is the product itself.
  have h_eq :
      (Set.image (fun p : X × Y => (p.1, p.2)) (Set.prod A B) :
        Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact hxy
    · intro hp
      refine ⟨p, hp, ?_⟩
      cases p with
      | mk x y => simp
  -- Apply `P1` for the product `A ×ˢ B` and rewrite using `h_eq`.
  simpa [h_eq] using (P1_prod (A := A) (B := B) hA hB)

theorem P2_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (interior (interior A))) := by
  exact
    P2_of_isOpen
      (A := interior (interior (interior A)))
      isOpen_interior

theorem P1_sUnion_union {X : Type*} [TopologicalSpace X] {𝒜 𝓑 : Set (Set X)} (hA : ∀ A ∈ 𝒜, P1 A) (hB : ∀ B ∈ 𝓑, P1 B) : P1 (⋃₀ (𝒜 ∪ 𝓑)) := by
  -- First, prove that every set belonging to `𝒜 ∪ 𝓑` satisfies `P1`.
  have h_union : ∀ S : Set X, S ∈ (𝒜 ∪ 𝓑 : Set (Set X)) → P1 S := by
    intro S hS
    cases hS with
    | inl hS𝒜 => exact hA S hS𝒜
    | inr hS𝓑 => exact hB S hS𝓑
  -- Apply `P1_sUnion` to the union family.
  simpa using
    (P1_sUnion (X := X) (𝒜 := (𝒜 ∪ 𝓑)) h_union)

theorem P3_Unionᵢ_closed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i) ∧ P3 (A i)) : P3 (⋃ i, A i) := by
  simpa using P3_Unionᵢ (A := A) (fun i => (hA i).2)

theorem P3_sUnion_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, IsOpen A) : P3 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P3`.
  have hP3 : ∀ A ∈ 𝒜, P3 A := by
    intro A hA_mem
    exact P3_of_isOpen (A := A) (hA A hA_mem)
  -- Apply the `P3_sUnion` lemma with this information.
  simpa using P3_sUnion (X := X) (𝒜 := 𝒜) hP3

theorem P1_sigma_set {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P1 A) : P1 {x : X | ∃ A ∈ S, x ∈ A} := by
  -- First, obtain `P1` for the union `⋃₀ S`.
  have hP1 : P1 (⋃₀ S) := P1_sUnion (X := X) (𝒜 := S) h
  -- Identify the σ–set with this union.
  have h_eq : ({x : X | ∃ A ∈ S, x ∈ A} : Set X) = ⋃₀ S := by
    ext x
    constructor
    · rintro ⟨A, hAS, hAx⟩
      exact Set.mem_sUnion.2 ⟨A, hAS, hAx⟩
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hAx⟩
      exact ⟨A, hAS, hAx⟩
  -- Transfer the `P1` property along this equality.
  simpa [h_eq] using hP1

theorem P1_iterate_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (closure (interior A))) := by
  intro x hx
  -- First, rewrite `hx` using idempotence of `closure`.
  have hx' : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx
  -- Show that `closure (interior A)` is contained in the needed closure.
  have h_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- Since `interior A` is open and contained in its closure,
    -- it is contained in the interior of that closure.
    have h_in :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- Taking closures preserves the inclusion.
    exact closure_mono h_in
  -- Apply the inclusion to obtain the desired membership.
  have hx'' := h_subset hx'
  simpa [closure_closure] using hx''

theorem P2_of_closure_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure (interior A))) : P2 A := by
  intro x hx
  exact h (subset_closure hx)

theorem exists_P3_within_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : ∃ B : Set X, B ⊆ closure A ∧ P3 B := by
  refine ⟨interior (closure A), ?_, ?_⟩
  ·
    exact interior_subset
  ·
    exact P3_of_isOpen (A := interior (closure A)) isOpen_interior