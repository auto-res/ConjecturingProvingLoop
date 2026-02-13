

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]  -- unfold the goal
  intro x hx
  -- From `P3` we know `A ⊆ interior (closure A)`.
  have h_subset : (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
    have hA_sub : (A : Set X) ⊆ interior (closure A) := hA
    exact closure_mono hA_sub
  exact h_subset hx