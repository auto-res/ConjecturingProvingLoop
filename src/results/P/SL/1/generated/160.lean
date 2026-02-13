

theorem Topology.interior_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (A : ι → Set X) :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hxi