

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P3 (X := X) A := by
  intro hP2
  unfold P2 at hP2
  unfold P3
  have hcl : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hcl
  exact fun x hx => hmono (hP2 hx)