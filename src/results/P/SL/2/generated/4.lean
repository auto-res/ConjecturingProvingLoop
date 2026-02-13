

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P3 A := by
  intro hA
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) := by
    have hcl : (A : Set X) ⊆ closure A := subset_closure
    exact interior_maximal hcl hA
  exact hsubset hxA