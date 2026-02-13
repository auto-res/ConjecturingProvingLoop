

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP3
    exact interior_eq_self_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hIntEq
    have hOpen : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    simpa using Topology.P3_of_isOpen (A := A) hOpen