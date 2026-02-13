

theorem Topology.P2_iff_P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  have h₁ := (Topology.P2_closed_iff_isOpen (A := closure (A : Set X)) hClosed)
  have h₂ := (Topology.P3_closed_iff_isOpen (A := closure (A : Set X)) hClosed)
  exact h₁.trans h₂.symm