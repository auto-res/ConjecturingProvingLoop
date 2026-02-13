

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  unfold Topology.P1
  intro x hx
  have h_sub : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact subset_closure
    simpa [interior_interior] using this
  have h_closure : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_sub
  exact h_closure hx