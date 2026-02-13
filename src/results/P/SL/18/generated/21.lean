

theorem P3_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_in : x ∈ interior (closure (A i)) := h i hxAi
  have hIncl : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    have hSub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  exact hIncl hx_in