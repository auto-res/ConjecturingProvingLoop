

theorem Topology.closure_eq_univ_of_closure_interior_eq_univ'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · -- `closure A` is certainly contained in `univ`.
    intro _ _
    trivial
  · -- Use the hypothesis together with monotonicity of `closure`.
    have h_sub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) (A := A)
    simpa [h] using h_sub