

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P2 s) → Topology.P2 (⋃₀ 𝒞) := by
  classical
  intro h𝒞
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  have hx_int : x ∈ interior (closure (interior S)) := (h𝒞 S hS_mem) hxS
  have hSub : interior (closure (interior S)) ⊆
      interior (closure (interior (⋃₀ 𝒞))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
  exact hSub hx_int