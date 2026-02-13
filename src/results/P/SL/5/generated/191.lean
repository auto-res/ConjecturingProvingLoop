

theorem closure_interior_iterate_six {X : Type*} [TopologicalSpace X] (A : Set X) :
    Nat.iterate (fun S : Set X => closure (interior S)) 6 A =
      closure (interior A) := by
  simp [Nat.iterate, Topology.closure_interior_idempotent]