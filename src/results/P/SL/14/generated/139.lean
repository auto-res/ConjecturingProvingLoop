

theorem Topology.P3_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (interior (closure (interior A)))) ↔
      Topology.P3 (closure (interior A)) := by
  -- Use the idempotence of the `closure ∘ interior` operator.
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3