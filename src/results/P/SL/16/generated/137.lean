

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A → Topology.P1 (X := X) (closure A) := by
  intro hP3
  dsimp [Topology.P1, Topology.P3] at hP3 ⊢
  intro x hxClA
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have h_subset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_subset hxClA