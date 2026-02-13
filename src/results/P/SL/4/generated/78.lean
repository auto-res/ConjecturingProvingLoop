

theorem P3_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen A :=
    ((Topology.P3_closed_iff_isOpen (A := A) hA).1) hP3
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_P1 (A := A) hOpen