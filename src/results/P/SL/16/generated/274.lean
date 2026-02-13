

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
  | inr hxCl =>
      exact
        (Topology.closure_interior_subset_closure (X := X) (A := A)) hxCl