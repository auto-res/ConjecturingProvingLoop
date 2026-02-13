

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_int : (x : X) ∈ interior (closure A) := h𝒜 A hA𝒜 hxA
  have h_subset :
      interior (closure A) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) := by
    apply interior_mono
    have h_closure :
        closure A ⊆ closure (⋃₀ 𝒜 : Set X) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
    exact h_closure
  exact h_subset hx_int