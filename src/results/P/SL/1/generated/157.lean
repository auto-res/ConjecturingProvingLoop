

theorem Topology.P1_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure (closure A)) := by
  intro hP1
  have h : Topology.P1 (closure A) := Topology.P1_closure (A := A) hP1
  simpa [closure_closure] using h