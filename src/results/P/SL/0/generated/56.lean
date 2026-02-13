

theorem P2_implies_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  have hmono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hcl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hcl
  exact hP2.trans hmono