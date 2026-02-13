

theorem P1_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 B := by
  constructor
  · intro hProd
    -- Extract `P1` for `B` from the product using the projection lemma.
    exact
      Topology.P1_of_P1_prod_right (A := A) (B := B) hA_nonempty hProd
  · intro hPB
    -- Build `P1` for the product from `P1 B` and the openness of `A`.
    exact
      Topology.P1_prod_left_open (A := A) (B := B) hA_open hPB

theorem P123_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    (Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B)) ↔
      (Topology.P1 B ∧ Topology.P2 B ∧ Topology.P3 B) := by
  -- Equivalences for each property with an open, nonempty left factor.
  have hP1Equiv :=
    Topology.P1_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  have hP2Equiv :=
    Topology.P2_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  have hP3Equiv :=
    Topology.P3_prod_left_open_iff (A := A) (B := B) hA_open hA_nonempty
  constructor
  · rintro ⟨hP1Prod, hP2Prod, hP3Prod⟩
    exact
      ⟨hP1Equiv.mp hP1Prod, hP2Equiv.mp hP2Prod, hP3Equiv.mp hP3Prod⟩
  · rintro ⟨hP1B, hP2B, hP3B⟩
    exact
      ⟨hP1Equiv.mpr hP1B, hP2Equiv.mpr hP2B, hP3Equiv.mpr hP3B⟩