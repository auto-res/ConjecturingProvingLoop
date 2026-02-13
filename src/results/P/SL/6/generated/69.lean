

theorem open_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP3
  exact (Topology.P3_closure_iff_open_closure (A := A)).1 hP3