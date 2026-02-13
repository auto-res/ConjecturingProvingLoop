

theorem closure_interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  have h_subset :
      interior (closure A) ⊆ interior (closure (interior (closure A))) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := closure A)
  have h_mono :
      closure (interior (closure A)) ⊆
        closure (interior (closure (interior (closure A)))) :=
    closure_mono h_subset
  exact h_mono hx