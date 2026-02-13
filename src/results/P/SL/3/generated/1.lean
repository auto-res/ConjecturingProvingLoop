

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  have h₁ : interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset (s := A))
  exact Set.Subset.trans hA h₁