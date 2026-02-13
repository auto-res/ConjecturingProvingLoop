

theorem Topology.closureInterior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : closure (interior A) = closure A := by
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.symm