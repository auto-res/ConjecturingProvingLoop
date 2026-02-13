

theorem Topology.iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : closure (A i) ⊆ closure (⋃ i, A i) :=
    closure_mono (Set.subset_iUnion A i)
  exact h_subset hx_i