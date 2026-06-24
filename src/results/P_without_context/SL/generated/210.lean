

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → (P1 (A := A) ∧ P3 (A := A)) := by
  intro hP2
  have hP1 : A ⊆ closure (interior A) :=
    subset_trans hP2 interior_subset
  have hcl : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hinter : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hcl
  have hP3 : A ⊆ interior (closure A) :=
    subset_trans hP2 hinter
  exact And.intro hP1 hP3