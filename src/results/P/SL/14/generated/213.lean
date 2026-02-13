

theorem Topology.P3_interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) ↔
      Topology.P3 (interior (closure A)) := by
  have hEq :
      (interior (closure (interior (closure A))) : Set X) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P3 (interior (closure (interior (closure A)))) ↔
        Topology.P3 (interior (closure (interior (closure A)))))