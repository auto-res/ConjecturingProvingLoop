

theorem Topology.P2_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (interior (closure (interior A)))) ↔
      Topology.P2 (closure (interior A)) := by
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P2 (closure (interior (closure (interior A)))) ↔
        Topology.P2 (closure (interior (closure (interior A)))))