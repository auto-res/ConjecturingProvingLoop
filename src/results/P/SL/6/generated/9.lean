

theorem P3_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A ↔ Topology.P2 A := by
  have h₁ : Topology.P3 A → Topology.P2 A := by
    intro h3
    dsimp [Topology.P3, Topology.P2] at h3 ⊢
    simpa [hA.interior_eq] using h3
  have h₂ : Topology.P2 A → Topology.P3 A := by
    intro h2
    exact P2_implies_P3 h2
  exact ⟨h₁, h₂⟩