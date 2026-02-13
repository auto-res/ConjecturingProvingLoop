

theorem P1_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) := by
  -- `A` is open, hence satisfies `P1`.
  have hA : Topology.P1 A := Topology.P1_of_open (A := A) hA_open
  -- Apply the existing product lemma for `P1`.
  exact Topology.P1_prod hA hB