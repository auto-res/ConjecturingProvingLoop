

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  open Set in
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_mono : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure_mono
  exact hP2.trans h_subset