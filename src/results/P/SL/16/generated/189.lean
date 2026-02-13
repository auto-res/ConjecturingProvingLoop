

theorem Topology.closure_interior_iUnion_subset {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} :
    (⋃ i, closure (interior (A i)) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (A i)` is contained in `interior (⋃ i, A i)`
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : (A i) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_sub
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_i