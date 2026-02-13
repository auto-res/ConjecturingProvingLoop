

theorem P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  have hcl :
      closure (interior (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
    apply closure_mono
    have : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact this
  exact hP1.trans hcl