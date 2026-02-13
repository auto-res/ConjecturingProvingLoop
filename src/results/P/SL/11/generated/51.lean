

theorem P2_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ IsOpen A := by
  -- Relate `P3` and openness for closed sets.
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_open_of_closed (A := A) hA
  constructor
  · intro hP2
    -- `P2` implies `P3`, then use the equivalence.
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (hP3Open.mp hP3)
  · intro hOpen
    -- An open set satisfies `P2`.
    exact Topology.P2_of_open (A := A) hOpen