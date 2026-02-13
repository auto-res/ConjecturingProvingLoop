

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3cl
  dsimp [Topology.P3] at hP3cl ⊢
  intro x hxA
  have hxCl : (x : X) ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3cl hxCl
  simpa [closure_closure] using hxInt