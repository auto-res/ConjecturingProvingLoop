

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure (interior A) = closure (interior (closure A)) := by
  calc
    closure (interior A)
        = closure A := (Topology.closure_eq_closure_interior_of_P2 (A := A) hP2).symm
    _ = closure (interior (closure A)) :=
      Topology.closure_eq_closure_interior_closure_of_P2 (A := A) hP2