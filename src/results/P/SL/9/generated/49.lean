

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_id : closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_idempotent (A := A)
  simpa [h_id] using hx