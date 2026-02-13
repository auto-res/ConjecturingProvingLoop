

theorem closure_interior_closure_eq_closure_interior_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = closure (interior A)) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- From the given equality we obtain `P1 A`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P1_of_closure_eq_closure_interior (A := A) h
  -- `P1` yields an identity relating the two closures we are interested in.
  have hEq :
      closure (A : Set X) = closure (interior (closure (A : Set X))) :=
    Topology.closure_eq_closure_interior_closure_of_P1 (A := A) hP1
  -- Rearrange the equality for convenient rewriting.
  have hEq' :
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
    simpa using hEq.symm
  -- Substitute and finish.
  simpa [hEq', h]