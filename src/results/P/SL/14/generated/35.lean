

theorem Topology.clopen_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A ∧ IsClosed A := by
  have h_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hP3
  exact ⟨h_open, hA_closed⟩