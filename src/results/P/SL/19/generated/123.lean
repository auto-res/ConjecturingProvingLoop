

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hInt =>
      exact (Topology.interior_closure_subset_closure (A := A)) hInt
  | inr hClosInt =>
      exact (Topology.closure_interior_subset_closure (A := A)) hClosInt