

theorem Topology.P1_iff_P2_and_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences obtained from the density of `interior A`.
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    (Topology.P2_iff_P1_of_denseInterior (X := X) (A := A) hDense).symm
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    (Topology.P3_iff_P1_of_dense (X := X) (A := A) hDense).symm
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := (hP1P2).1 hP1
    have hP3 : Topology.P3 A := (hP1P3).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact (hP1P2).2 hP2