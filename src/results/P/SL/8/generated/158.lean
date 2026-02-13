

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP2A := h𝒜 A hA_mem
  have hxIntClA : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_inclusion :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- `interior A` is contained in `interior (⋃₀ 𝒜)`
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      have h_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact interior_mono h_subset
    -- Taking closures preserves inclusions
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_subset
    -- And interiors are monotone
    exact interior_mono h_closure_subset
  exact h_inclusion hxIntClA