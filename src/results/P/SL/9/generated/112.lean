

theorem Topology.closureInterior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (A := A)) :
    closure (interior A) = closure A := by
  exact
    ((Topology.P1_iff_closureInterior_eq_closure (A := A)).1
      (Topology.P2_implies_P1 hP2))