

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hA
  have h1 : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  have h2 : interior (closure (interior (A : Set X))) ⊆ interior (closure A) :=
    interior_mono h1
  exact subset_trans hA h2