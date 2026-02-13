

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) :=
    interior_mono (Set.subset_iUnion A i)
  exact hsubset hxInt