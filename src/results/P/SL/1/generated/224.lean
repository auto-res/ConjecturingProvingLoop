

theorem Topology.P2_iff_P3_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- `P2 A` is equivalent to `P3 A ∧ closure A = closure (interior A)`.
  have h := Topology.P2_iff_P3_and_closure_eq_closure_interior (A := A)
  constructor
  · intro hP2
    exact (h.mp hP2).1
  · intro hP3
    exact
      Topology.P2_of_P3_and_closure_eq_closure_interior
        (A := A) hP3 hEq