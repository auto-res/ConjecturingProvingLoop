

theorem Topology.P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    exact Topology.interior_eq_self_of_closed_and_P2 (A := A) hA_closed hP2
  · intro hInt
    have hA_open : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.P2_of_isOpen (A := A) hA_open