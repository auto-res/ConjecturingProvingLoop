

theorem P2_iff_P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have h₁ : Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  have h₂ : Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact h₁.trans h₂.symm