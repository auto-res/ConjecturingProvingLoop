

theorem P1_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P1 A := by
  -- First, extract `P2` for `A` from the product assumption.
  have hP2A : Topology.P2 A :=
    Topology.P2_of_P2_prod_left (A := A) (B := B) hB hP2
  -- Since `P2` implies `P1`, we obtain the desired result.
  exact Topology.P2_implies_P1 (A := A) hP2A