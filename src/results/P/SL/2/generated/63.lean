

theorem Topology.isOpen_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P3 A := by
  intro hOpen
  have hP3Closure : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact (Topology.P3_closure_implies_P3 (A := A)) hP3Closure