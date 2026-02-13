

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure A) := (h A hA_mem) hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    have h_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P1_and_P3_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := by
  intro x hxA
  -- `P3` gives that `x ∈ interior (closure A)`.
  have hx_int_clA : x ∈ interior (closure A) := h3 hxA
  -- From `P1` we have `A ⊆ closure (interior A)`, hence
  -- `closure A ⊆ closure (interior A)`.
  have h_cl_subset : closure A ⊆ closure (interior A) := by
    have h : (A : Set X) ⊆ closure (interior A) := h1
    simpa using closure_mono h
  -- Taking interiors preserves inclusion.
  have h_int_subset :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_cl_subset
  -- Apply the inclusion to obtain the desired membership.
  exact h_int_subset hx_int_clA