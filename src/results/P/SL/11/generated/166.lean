

theorem P123_prod_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ×ˢ B) ∧ Topology.P2 (A ×ˢ B) ∧ Topology.P3 (A ×ˢ B) := by
  exact
    ⟨Topology.P1_prod_open (A := A) (B := B) hA hB,
      Topology.P2_prod_open (A := A) (B := B) hA hB,
      Topology.P3_prod_open (A := A) (B := B) hA hB⟩