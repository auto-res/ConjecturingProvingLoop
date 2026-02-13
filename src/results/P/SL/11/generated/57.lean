

theorem P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxA
  have hxCl : x ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3 hxCl
  simpa [closure_closure] using hxInt