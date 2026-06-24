

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P1 A ∧ P3 A := by
  intro hP2
  have hP1 : P1 A := by
    intro x hx
    have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
    exact interior_subset hx_in
  have hP3 : P3 A := by
    intro x hx
    have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
      have hsubset_closure : closure (interior A) ⊆ closure A := by
        have hsub : interior A ⊆ A := interior_subset
        exact closure_mono hsub
      exact interior_mono hsubset_closure
    exact hsubset hx_in
  exact And.intro hP1 hP3