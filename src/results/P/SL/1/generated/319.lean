

theorem Topology.P3_closure_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 (closure A) := by
  intro hP2
  have hClosed : IsClosed (closure A) := isClosed_closure
  have hOpen : IsOpen (closure A) :=
    Topology.isOpen_of_P2_of_isClosed (A := closure A) hClosed hP2
  exact Topology.P3_of_isOpen (A := closure A) hOpen