

theorem P3_prod_right_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB_open : IsOpen B) (hB_nonempty : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact Topology.P3_of_P3_prod_left (A := A) (B := B) hB_nonempty hProd
  · intro hA
    exact Topology.P3_prod_right_open (A := A) (B := B) hA hB_open