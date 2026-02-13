

theorem Topology.closureInterior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) : closure (interior A) = closure A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.symm