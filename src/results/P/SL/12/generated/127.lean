

theorem Topology.closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  -- `P1` for `A` yields `P1` for `closure A`.
  have hP1_closure : Topology.P1 (X := X) (closure A) :=
    Topology.P1_closure_of_P1 (X := X) (A := A) hA
  -- Apply the equality given by `P1` to `closure A`.
  have h_eq :
      closure (closure (A : Set X)) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := closure A) hP1_closure
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h_eq