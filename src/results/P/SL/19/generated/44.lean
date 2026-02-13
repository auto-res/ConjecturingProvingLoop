

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h1 :
      interior (closure (interior (closure A))) = interior (closure A) :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)
  have h2 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := interior (closure A))
  simpa [h1] using h2