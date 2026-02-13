

theorem Topology.isClopen_of_isClosed_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsClopen A := by
  -- From `P3` and closedness we obtain that `A` is open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact ⟨hA_closed, hA_open⟩