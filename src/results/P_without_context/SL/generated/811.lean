

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have h₁ : A ⊆ interior (closure (interior A)) := by
    simpa [Topology.P2] using hP2
  have h₂ : A ⊆ closure (interior A) :=
    (Set.Subset.trans h₁
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)))
  simpa [Topology.P1] using h₂