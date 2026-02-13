

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