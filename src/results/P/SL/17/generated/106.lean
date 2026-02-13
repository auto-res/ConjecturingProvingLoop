

theorem Topology.P1_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure A))))) := by
  -- First, simplify the nested `closure ∘ interior` expression using idempotence.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_idempotent (A := closure A))
  -- We already know `P1` holds for `closure (interior (closure A))`.
  have hP1 : Topology.P1 (closure (interior (closure A))) :=
    Topology.P1_closure_interior_closure (A := A)
  -- Transport the property along the established equality.
  simpa [h_eq] using hP1