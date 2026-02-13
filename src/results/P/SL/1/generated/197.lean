

theorem Topology.P2_iff_isClopen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ IsClopen A := by
  constructor
  · intro hP2
    have hOpen : IsOpen A :=
      Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
    exact ⟨hA, hOpen⟩
  · intro hClopen
    exact Topology.P2_of_isOpen (A := A) hClopen.2