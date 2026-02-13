

theorem open_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      IsOpen (closure (A : Set X)) →
        IsOpen (closure (interior A)) := by
  intro hP1 hOpen
  -- From `P1`, we obtain the equality of closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Rewrite using this equality to transfer openness.
  simpa [hEq] using hOpen