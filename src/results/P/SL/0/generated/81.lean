

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro h𝒜
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := h𝒜 A hA_mem hxA
  have h_mono :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    have h_int_sub :
        interior (A : Set X) ⊆ interior (⋃₀ 𝒜 : Set X) := by
      have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_mono hx_cl