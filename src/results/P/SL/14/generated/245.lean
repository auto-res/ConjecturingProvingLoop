

theorem Topology.P1_interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure A)))) ↔
      Topology.P1 (interior (closure A)) := by
  have hEq :
      (interior (closure (interior (closure A))) : Set X) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P1 (interior (closure (interior (closure A)))) ↔
        Topology.P1 (interior (closure (interior (closure A)))))