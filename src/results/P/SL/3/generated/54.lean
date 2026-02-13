

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_cl : (x : X) ∈ closure (interior A) := h𝒜 A hA𝒜 hxA
  have h_subset :
      closure (interior A) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    have h_int : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
    exact h_int
  exact h_subset hx_cl