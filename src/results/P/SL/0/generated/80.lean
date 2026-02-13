

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := h𝒜 A hA_mem hxA
  have h_mono :
      interior (closure (A : Set X)) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) := by
    have h_closure :
        closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_mono hx_int