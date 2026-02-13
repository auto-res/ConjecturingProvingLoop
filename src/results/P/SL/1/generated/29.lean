

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  have hA_subset : (A : Set X) ⊆ interior (closure A) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  have hclosure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hA_subset
  exact hclosure_subset hx