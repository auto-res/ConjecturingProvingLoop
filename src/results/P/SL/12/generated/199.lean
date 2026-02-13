

theorem Topology.iUnion_closure_subset_closure_iUnion {X ι : Type*}
    [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `A i ⊆ ⋃ j, A j`
  have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Taking closures preserves the inclusion.
  have h_closure : closure (A i : Set X) ⊆ closure (⋃ j, A j) :=
    closure_mono h_subset
  exact h_closure hx_i