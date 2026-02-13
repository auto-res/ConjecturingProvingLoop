

theorem Topology.closure_eq_univ_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · intro x hx
    have hx_int : x ∈ interior (closure A) := by
      simpa [h] using hx
    exact (interior_subset : interior (closure A) ⊆ closure A) hx_int