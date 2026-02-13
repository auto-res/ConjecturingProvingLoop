

theorem P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : Topology.P2 A ↔ Topology.P3 A := by
  -- `P1` yields the key closure equality.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Use the previously established equivalence under this equality.
  simpa using
    (Topology.P2_iff_P3_of_closure_eq_closure_interior (A := A) hEq)