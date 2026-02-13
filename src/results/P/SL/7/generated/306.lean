

theorem Topology.closureInterior_iter5_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  simpa [Topology.closureInteriorClosureInterior_eq_closureInterior] using
    (by
      simp [Topology.closureInteriorClosureInterior_eq_closureInterior])