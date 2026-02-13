

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P1 s) → Topology.P1 (⋃₀ 𝒞) := by
  intro h𝒞
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  -- From `P1 S` we obtain membership in `closure (interior S)`.
  have hx_closureS : x ∈ closure (interior S) := (h𝒞 S hS_mem) hxS
  -- We show that `closure (interior S)` is contained in
  -- `closure (interior (⋃₀ 𝒞))`.
  have hSub : closure (interior S) ⊆ closure (interior (⋃₀ 𝒞)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
  exact hSub hx_closureS