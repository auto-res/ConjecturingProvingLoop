

theorem P1_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB_open : IsOpen B) :
    Topology.P1 (A ×ˢ B) := by
  -- Translate the openness of `B` into the `P1` property.
  have hB : Topology.P1 B := Topology.P1_of_open (A := B) hB_open
  -- Conclude using the general product lemma for `P1`.
  exact Topology.P1_prod hA hB