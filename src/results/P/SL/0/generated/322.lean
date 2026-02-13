

theorem closed_P2_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hP2
  -- A closed set with property `P2` is open, by a previously established lemma.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed) hP2
  -- A clopen set satisfies all three properties `P1`, `P2`, and `P3`.
  exact Topology.clopen_has_all_Ps (X := X) (A := A) hOpen hClosed