

theorem P2_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_in : x ∈ interior (closure (interior (A i))) := h i hxAi
  have hIncl :
      interior (closure (interior (A i)))
        ⊆ interior (closure (interior (⋃ j, A j))) := by
    apply interior_mono
    have hSub :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      apply closure_mono
      have :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact this
    exact hSub
  exact hIncl hx_in