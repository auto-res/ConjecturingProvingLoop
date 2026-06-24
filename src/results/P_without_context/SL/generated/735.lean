

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) :=
by
  intro hP2
  have hsubset : closure (interior (A : Set X)) ⊆ closure (A) := by
    apply closure_mono
    exact interior_subset
  have hsubset₂ :
      interior (closure (interior (A : Set X))) ⊆ interior (closure (A)) :=
    interior_mono hsubset
  exact Set.Subset.trans hP2 hsubset₂