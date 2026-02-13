

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          have h :=
            Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
              (X := X) (A := A)
          simpa [h]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))