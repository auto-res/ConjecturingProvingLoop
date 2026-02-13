

theorem P2_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ (Topology.P2 A ∧ Topology.P2 B) := by
  constructor
  · intro hP2Prod
    have hP2A : Topology.P2 A :=
      Topology.P2_of_P2_prod_left (A := A) (B := B) hB hP2Prod
    have hP2B : Topology.P2 B :=
      Topology.P2_of_P2_prod_right (A := A) (B := B) hA hP2Prod
    exact ⟨hP2A, hP2B⟩
  · rintro ⟨hP2A, hP2B⟩
    exact Topology.P2_prod (A := A) (B := B) hP2A hP2B