

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  -- Use `P2` for the particular set `A`.
  have hxInt : x ∈ interior (closure (interior A)) := h𝒜 A hA_mem hxA
  -- `interior A` is contained in the interior of the union.
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have h_sub : A ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact interior_mono h_sub
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  -- Apply `interior_mono` once more.
  have h_int_subset' :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  exact h_int_subset' hxInt