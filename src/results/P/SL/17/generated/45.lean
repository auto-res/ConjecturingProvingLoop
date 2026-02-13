

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  unfold Topology.P1
  intro x hx
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx