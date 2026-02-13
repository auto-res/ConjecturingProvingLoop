

theorem Topology.isClosed_P3_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P3 A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hP3
  have hOpen : IsOpen (A : Set X) :=
    Topology.isClosed_P3_implies_isOpen (A := A) hClosed hP3
  exact Topology.isClosed_isOpen_implies_frontier_eq_empty (A := A) hClosed hOpen