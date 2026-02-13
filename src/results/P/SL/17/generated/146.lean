

theorem Topology.P2_closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (interior A)))) ↔
      Topology.P2 (closure (interior A)) := by
  have hEq : closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  simpa [hEq]