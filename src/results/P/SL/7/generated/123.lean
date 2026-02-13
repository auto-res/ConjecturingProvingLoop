

theorem Topology.P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP3
    exact Topology.interior_eq_of_P3_closed (A := A) hA hP3
  · intro hInt
    -- From `interior A = A` we get that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hInt] using this
    -- An open set satisfies `P3`.
    exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).2