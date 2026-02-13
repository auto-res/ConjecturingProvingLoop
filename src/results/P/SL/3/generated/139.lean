

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P2 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have h₁ :=
    (P3_closure_interior_iff_P2_closure_interior (A := A))
  have h₂ :=
    (P3_closure_interior_iff_isOpen_closure_interior (A := A))
  simpa using h₁.symm.trans h₂