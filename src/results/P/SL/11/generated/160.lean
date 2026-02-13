

theorem P2_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ×ˢ B) := by
  -- The open set `A` automatically satisfies `P2`.
  have hA : Topology.P2 A := Topology.P2_of_open (A := A) hA_open
  -- Apply the existing product lemma for `P2`.
  exact Topology.P2_prod (A := A) (B := B) hA hB