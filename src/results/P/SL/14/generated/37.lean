

theorem Topology.P2_iff_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- Using existing equivalences between `P2`, `P3`, and openness for closed sets.
  have hP2 := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  have hP3 := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  constructor
  · intro hPA2
    -- From `P2 A` we get `IsOpen A`, then derive `P3 A`.
    have hOpen : IsOpen A := (hP2).1 hPA2
    exact (hP3).2 hOpen
  · intro hPA3
    -- From `P3 A` we get `IsOpen A`, then derive `P2 A`.
    have hOpen : IsOpen A := (hP3).1 hPA3
    exact (hP2).2 hOpen