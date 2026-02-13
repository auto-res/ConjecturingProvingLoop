

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have hint : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono hcl
  exact hP2.trans hint