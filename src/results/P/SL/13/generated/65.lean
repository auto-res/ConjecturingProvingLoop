

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- Collapse the innermost three-layer expression.
  have h_inner :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Rewrite the goal using `h_inner`, then finish with the two-layer lemma.
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure A))) := by
          simpa [h_inner]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))