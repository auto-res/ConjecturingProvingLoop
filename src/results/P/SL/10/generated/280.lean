

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have h_subset :
      interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono (Set.subset_iUnion (fun j ↦ A j) i)
  exact h_subset hxInt