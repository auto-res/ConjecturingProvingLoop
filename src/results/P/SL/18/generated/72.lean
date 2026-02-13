

theorem P3_implies_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  -- From `P3` and closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_open hA_closed).1 hP3
  -- For an open set, `P2` holds.
  exact Topology.P2_of_open hOpen