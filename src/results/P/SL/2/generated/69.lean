

theorem Topology.isClosed_P2_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → Topology.P2 A → interior A = A := by
  intro hClosed hP2
  have hOpen : IsOpen A := Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  simpa using hOpen.interior_eq