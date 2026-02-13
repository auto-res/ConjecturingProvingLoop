

theorem open_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2
  exact (Topology.P2_closure_iff_open_closure (A := A)).1 hP2