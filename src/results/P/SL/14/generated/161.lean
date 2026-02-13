

theorem Topology.P1_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior A)))) ↔
      Topology.P1 (closure (interior A)) := by
  -- `closure ∘ interior` is idempotent, hence the two sets coincide.
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  -- After rewriting with this equality, both sides are definitionally equal.
  simpa [hEq] using
    (Iff.rfl :
      Topology.P1 (closure (interior (closure (interior A)))) ↔
        Topology.P1 (closure (interior (closure (interior A)))))