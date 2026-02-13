

theorem P2_closure_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ : Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
    simpa using (Topology.P2_iff_P3_closure (A := A))
  have h₂ : Topology.P3 (closure A) ↔ IsOpen (closure A) := by
    simpa using (Topology.P3_closure_iff_open (A := A))
  exact h₁.trans h₂