

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