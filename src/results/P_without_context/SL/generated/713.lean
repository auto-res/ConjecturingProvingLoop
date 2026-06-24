

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  unfold P2 at hP2
  unfold P3
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_interior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact Set.Subset.trans hP2 h_interior