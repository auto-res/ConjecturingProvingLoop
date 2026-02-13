

theorem P2_iff_P3_of_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔
      Topology.P3 (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have h₁ :
      Topology.P2 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) hClosed
  have h₂ :
      Topology.P3 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) hClosed
  exact h₁.trans h₂.symm