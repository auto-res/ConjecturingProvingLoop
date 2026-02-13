

theorem P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hClosureP3
  dsimp [Topology.P3] at hClosureP3 ⊢
  intro x hxA
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hxInterior : (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hClosureP3 hxClosure
  simpa [closure_closure] using hxInterior