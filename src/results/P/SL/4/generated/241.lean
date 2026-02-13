

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  have h₁ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_closed (A := A) hA
  have h₂ : Topology.P3 A ↔ interior A = A :=
    Topology.P3_closed_iff_interior_eq (A := A) hA
  exact h₁.trans h₂