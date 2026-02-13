

theorem closure_open_satisfies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  have hSub : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  exact closure_mono hSub