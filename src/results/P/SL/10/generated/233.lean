

theorem Topology.closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_sub : (A i) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_sub : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono h_sub
  exact h_closure_sub hx_i