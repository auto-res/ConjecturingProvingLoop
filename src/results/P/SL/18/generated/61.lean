

theorem P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3Clos
  dsimp [Topology.P3] at hP3Clos ⊢
  intro x hxA
  have hxClosure : x ∈ closure A :=
    (subset_closure : A ⊆ closure A) hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3Clos hxClosure
  simpa [closure_closure] using hxInt