

theorem P3_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness we obtain that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_open_of_closed (A := A) hA).1 hP3
  -- On an open set, `P1` and `P3` are equivalent.
  exact (Topology.P1_iff_P3_of_isOpen (A := A) hOpen).mpr hP3