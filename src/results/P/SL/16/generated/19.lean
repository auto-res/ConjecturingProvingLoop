

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) → Topology.P3 (X := X) A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure ⊢
  intro x hxA
  have hxClosure : x ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3Closure hxClosure
  simpa [closure_closure] using hxInt