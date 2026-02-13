

theorem P123_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  -- Individual equivalences for each property with an open, nonempty right factor.
  have hP1Equiv :=
    Topology.P1_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  have hP2Equiv :=
    Topology.P2_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  have hP3Equiv :=
    Topology.P3_prod_right_open_iff (A := A) (B := B) hB_open hB_nonempty
  constructor
  · rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    exact
      ⟨hP1Equiv.mp hP1Prod, hP2Equiv.mp hP2Prod, hP3Equiv.mp hP3Prod⟩
  · rintro ⟨hP1A, hP2A, hP3A⟩
    exact
      ⟨hP1Equiv.mpr hP1A, hP2Equiv.mpr hP2A, hP3Equiv.mpr hP3A⟩