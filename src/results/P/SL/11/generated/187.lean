

theorem P1_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hB : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ (Topology.P1 A ∧ Topology.P1 B) := by
  constructor
  · intro hP1Prod
    have hP1A : Topology.P1 A :=
      Topology.P1_of_P1_prod_left (A := A) (B := B) hB hP1Prod
    have hP1B : Topology.P1 B :=
      Topology.P1_of_P1_prod_right (A := A) (B := B) hA hP1Prod
    exact ⟨hP1A, hP1B⟩
  · rintro ⟨hP1A, hP1B⟩
    exact Topology.P1_prod hP1A hP1B