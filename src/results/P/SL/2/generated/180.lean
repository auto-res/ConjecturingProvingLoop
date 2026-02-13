

theorem Topology.isOpen_closure_interior_implies_P2_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior A)) → Topology.P2 (closure (interior A)) := by
  intro hOpen
  exact
    (Topology.P2_closure_interior_iff_isOpen_closure_interior (A := A)).2 hOpen