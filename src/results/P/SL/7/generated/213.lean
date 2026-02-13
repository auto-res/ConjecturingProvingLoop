

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P3 s) → Topology.P3 (⋃₀ 𝒞) := by
  intro h𝒞
  dsimp [Topology.P3]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  have hx_int : x ∈ interior (closure S) := h𝒞 S hS_mem hxS
  have hSub : interior (closure S) ⊆ interior (closure (⋃₀ 𝒞)) := by
    apply interior_mono
    have : (closure S : Set X) ⊆ closure (⋃₀ 𝒞) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
    exact this
  exact hSub hx_int