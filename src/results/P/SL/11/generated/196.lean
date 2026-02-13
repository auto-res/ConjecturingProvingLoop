

theorem P3_of_P2_prod_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hP2 : Topology.P2 (A ×ˢ B)) :
    Topology.P3 B := by
  -- First, upgrade the product assumption from `P2` to `P3`.
  have hP3Prod : Topology.P3 (A ×ˢ B) :=
    Topology.P2_implies_P3 (A := A ×ˢ B) hP2
  -- Use the existing projection lemma for `P3` to obtain the result.
  exact Topology.P3_of_P3_prod_right (A := A) (B := B) hA hP3Prod