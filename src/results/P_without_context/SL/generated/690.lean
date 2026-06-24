

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) :=
by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hclosure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono hclosure
  exact Set.Subset.trans hP2 hmono