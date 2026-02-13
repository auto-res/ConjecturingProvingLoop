

theorem interior_closure_interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ∩ interior (closure A) =
      interior (closure (interior A)) := by
  apply (Set.inter_eq_left).2
  exact
    Topology.interior_closure_interior_subset_interior_closure
      (X := X) (A := A)