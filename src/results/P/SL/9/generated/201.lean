

theorem Topology.closure_iInter_eq_iInter_of_isClosed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, IsClosed (𝒜 i)) :
    closure (⋂ i, 𝒜 i) = ⋂ i, 𝒜 i := by
  have hClosed : IsClosed (⋂ i, 𝒜 i) := isClosed_iInter h𝒜
  simpa [hClosed.closure_eq]