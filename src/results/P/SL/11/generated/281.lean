

theorem P1_prod_right_open_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      Topology.P1_of_P1_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hPA
    exact
      Topology.P1_prod_right_open (A := A) (B := B) hPA hB_open