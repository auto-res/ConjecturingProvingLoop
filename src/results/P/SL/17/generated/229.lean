

theorem Topology.P3_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (closure (interior (closure (interior A)))) ↔
      Topology.P3 (closure (interior A)) := by
  -- The core equality coming from idempotence of `closure ∘ interior`.
  have hEq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3