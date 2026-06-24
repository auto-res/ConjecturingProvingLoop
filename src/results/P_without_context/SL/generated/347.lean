

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  exact
    Set.Subset.trans hA
      (by
        have hclosure : closure (interior (A : Set X)) ⊆ closure A :=
          closure_mono (by
            exact interior_subset)
        have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
          interior_mono hclosure
        simpa using hmono)