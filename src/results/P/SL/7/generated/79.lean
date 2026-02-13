

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  have : (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hP3 (subset_closure hx)
  simpa [closure_closure] using this