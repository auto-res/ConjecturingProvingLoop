

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