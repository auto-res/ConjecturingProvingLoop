

theorem P2_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      Topology.P2_of_P2_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hA
    exact Topology.P2_prod_right_open (A := A) (B := B) hA hB_open