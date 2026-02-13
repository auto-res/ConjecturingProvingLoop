

theorem P1_interior_closure_iff_P3_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) ↔
      Topology.P3 (interior (closure (A : Set X))) := by
  have h₁ := P1_interior_closure_iff_P2_interior_closure (A := A)
  have h₂ := P3_interior_closure_iff_P2_interior_closure (A := A)
  simpa using h₁.trans h₂.symm