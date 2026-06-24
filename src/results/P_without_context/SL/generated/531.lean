

theorem P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  have h_aux : interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
    have h_closure : closure (interior (A : Set X)) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure
  exact hA.trans h_aux