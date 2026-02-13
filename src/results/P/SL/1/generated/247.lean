

theorem Topology.P2_iff_P3_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P2 A ↔ Topology.P1 A :=
    (Topology.P2_iff_P1_of_isClopen (A := A) hA)
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    (Topology.P3_iff_P1_of_isClopen (A := A) hA).symm
  exact h₁.trans h₂