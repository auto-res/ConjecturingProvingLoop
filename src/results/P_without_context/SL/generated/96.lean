

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P3 (X:=X) A := by
  intro hA
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_interior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact Set.Subset.trans hA h_interior