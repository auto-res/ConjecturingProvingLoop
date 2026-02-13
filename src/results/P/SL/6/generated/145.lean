

theorem open_of_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) → IsOpen (closure (interior A)) := by
  intro hP2
  exact
    (Topology.P2_closure_interior_iff_open_closure_interior (A := A)).1 hP2