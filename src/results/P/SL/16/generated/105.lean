

theorem Topology.iUnion_interior_subset_interior_iUnion
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have h_subset : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_subset
  exact h_int_subset hxInt