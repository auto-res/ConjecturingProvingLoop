

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Use the hypothesis on the chosen index.
  have hx' : x ∈ interior (closure (A i)) := hA i hxAi
  -- Relate the two interiors that appear.
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ i, A i)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Conclude by the inclusion.
  exact hsubset hx'