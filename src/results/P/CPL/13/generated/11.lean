

theorem P2_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP2i : Topology.P2 (A i) := h i
  have hx_in : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  have h_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact h_subset hx_in