

theorem Topology.P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (A := A) → Topology.P3 (X := X) (A := A) := by
  intro hP2
  have hInclusion : (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
    have hClosure : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono hClosure
  exact Set.Subset.trans hP2 hInclusion