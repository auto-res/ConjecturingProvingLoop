

theorem Topology.P2_iff_boundary_empty_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro hP2
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
    simpa using
      (boundary_eq_empty_of_isClopen (A := A) hOpen hA_closed)
  · intro hBoundary
    have hClopen :=
      (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
    exact Topology.P2_of_isOpen (A := A) hClopen.1