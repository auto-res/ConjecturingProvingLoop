

theorem closure_interior_idempotent_five {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  simp [Topology.closure_interior_idempotent]