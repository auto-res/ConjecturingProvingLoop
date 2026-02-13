

theorem P1_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X]
    (A : ι → Set X) (h : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hPi : (A i : Set X) ⊆ closure (interior (A i)) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hPi hxAi
  have h_mono : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have : interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact h_mono hx_cl