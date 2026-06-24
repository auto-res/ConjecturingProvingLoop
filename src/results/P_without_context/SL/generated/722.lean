

theorem P2_implies_P1_and_P3 {A : Set X} :
    P2 (A) → P1 (A) ∧ P3 (A) := by
  intro hP2
  have hP1 : P1 A := Set.Subset.trans hP2 interior_subset
  have hP3 : P3 A := by
    have h_closure_mono : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have h_interior_mono :
        interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h_closure_mono
    exact Set.Subset.trans hP2 h_interior_mono
  exact And.intro hP1 hP3