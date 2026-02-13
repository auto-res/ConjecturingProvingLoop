

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  -- From `P3` for `A` we get `P1` for `closure A`.
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_implies_P1_closure (X := X) (A := A) hA
  -- Apply the equality obtained from `P1`.
  have hEq :
      closure (closure (A : Set X)) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hEq