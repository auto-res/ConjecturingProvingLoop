

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A : Set X, A ∈ 𝒜 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA𝒜, hxA⟩
  have hx_int : (x : X) ∈ interior (closure (interior A)) :=
    h𝒜 A hA𝒜 hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) := by
    have h_closure :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜 : Set X)) := by
      apply closure_mono
      have h_int : interior A ⊆ interior (⋃₀ 𝒜 : Set X) := by
        apply interior_mono
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA𝒜, hy⟩
      exact h_int
    exact interior_mono h_closure
  exact h_subset hx_int