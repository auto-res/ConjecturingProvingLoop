

theorem interior_closure_frontier_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (frontier A)) = interior (frontier A) := by
  have h : closure (frontier A) = frontier A :=
    closure_frontier_eq_frontier (X := X) (A := A)
  simpa [h]