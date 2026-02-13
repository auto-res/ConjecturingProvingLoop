

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (hA A hA_mem) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    have : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hx_closure