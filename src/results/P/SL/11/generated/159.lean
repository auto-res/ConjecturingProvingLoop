

theorem P2_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ×ˢ B) := by
  have hB : Topology.P2 B := Topology.P2_of_open (A := B) hB_open
  exact Topology.P2_prod (A := A) (B := B) hA hB