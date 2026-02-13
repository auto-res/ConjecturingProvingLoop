

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (closure (A i)) : Set X) ⊆
      interior (closure (⋃ i, A i)) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in `closure (⋃ j, A j)`.
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Applying `interior_mono` yields the desired inclusion on interiors.
  have h_int_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_i