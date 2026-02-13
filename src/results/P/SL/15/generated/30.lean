

theorem closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_subset : interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A)
  have h_mono : closure (interior A) ⊆
      closure (interior (closure (interior A))) :=
    closure_mono h_subset
  exact h_mono hx