

theorem P2_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P2`, we have `A ⊆ interior (closure (interior A))`.
  have h_subset : (A : Set X) ⊆ interior (closure (interior A)) := hA
  -- Taking closures yields the desired inclusion, modulo re-writing with idempotency.
  simpa [Topology.closure_interior_idempotent (X := X) (A := A)]
    using (closure_mono h_subset)