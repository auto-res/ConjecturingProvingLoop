

theorem P2_imp_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact Set.Subset.trans hP2 hsubset
  have hP3 : Topology.P3 A := by
    have hclosure_subset : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have hInteriorMono : interior (closure (interior A)) ⊆ interior (closure A) := by
      apply interior_mono
      exact hclosure_subset
    intro x hx
    exact hInteriorMono (hP2 hx)
  exact And.intro hP1 hP3