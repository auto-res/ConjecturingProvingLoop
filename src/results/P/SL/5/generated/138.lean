

theorem union_interior_closure_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  | inr hxCl =>
      have hsubset : closure (interior A) ⊆ closure A :=
        Topology.closure_interior_subset_closure (X := X) A
      exact hsubset hxCl