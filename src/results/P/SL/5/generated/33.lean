

theorem interior_closure_idempotent_four {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  simp [Topology.interior_closure_idempotent]