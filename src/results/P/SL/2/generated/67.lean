

theorem Topology.isOpen_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hOpen
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).2 hOpen
  exact
    (Topology.isClosed_P3_implies_P2 (A := closure (A : Set X))) hClosed hP3