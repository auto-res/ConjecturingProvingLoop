

theorem Topology.interiorClosure_iter3_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior
      (closure (interior (closure A))))))) = interior (closure A) := by
  have h₁ :=
    Topology.interiorClosure_iter2_idempotent
      (A := interior (closure A))
  have h₂ := Topology.interiorClosure_idempotent (A := A)
  simpa using h₁.trans h₂