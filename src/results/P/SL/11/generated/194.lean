

theorem P3_of_P2_prod_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hB : B.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P3 A := by
  -- Upgrade the product hypothesis from `P2` to `P3`.
  have hP3Prod : Topology.P3 (A ×ˢ B) :=
    Topology.P2_implies_P3 (A := A ×ˢ B) hP2
  -- Use the existing projection lemma for `P3`.
  exact Topology.P3_of_P3_prod_left (A := A) (B := B) hB hP3Prod