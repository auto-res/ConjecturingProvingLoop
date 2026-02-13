

theorem Topology.P3_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  constructor
  · intro h
    simpa [h_eq] using h
  · intro h
    simpa [h_eq] using h