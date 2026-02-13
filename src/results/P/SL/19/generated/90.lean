

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) →
      closure (interior (closure A)) = closure (interior A) := by
  intro hP1
  have hInt :
      interior (closure A) = interior (closure (interior A)) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := A) hP1
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := by
          simpa [hInt]
    _ = closure (interior A) :=
      Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A)