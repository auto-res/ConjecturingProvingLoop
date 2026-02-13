

theorem closed_P3_imp_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A ∧ IsClosed A := by
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  exact And.intro hOpen hA_closed