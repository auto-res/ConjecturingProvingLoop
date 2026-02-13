

theorem Topology.interior_closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_closure : closure (A i) ⊆ closure (⋃ j, A j) := by
    have h_subset : A i ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono h_subset
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure
  exact h_subset hx_i