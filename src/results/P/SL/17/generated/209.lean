

theorem Topology.P1_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  constructor
  · intro h
    simpa [h_eq] using h
  · intro h
    simpa [h_eq] using h