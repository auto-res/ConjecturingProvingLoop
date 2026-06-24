

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  have hcl : closure (interior (A : Set X)) ⊆ closure A := by
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  have hint : interior (closure (interior (A : Set X))) ⊆ interior (closure A) :=
    interior_mono hcl
  exact subset_trans hA hint