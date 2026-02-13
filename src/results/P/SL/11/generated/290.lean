

theorem P3_prod_left_open_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hA_nonempty : A.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 B := by
  constructor
  · intro hProd
    exact Topology.P3_of_P3_prod_right (A := A) (B := B) hA_nonempty hProd
  · intro hPB
    exact Topology.P3_prod_left_open (A := A) (B := B) hA_open hPB