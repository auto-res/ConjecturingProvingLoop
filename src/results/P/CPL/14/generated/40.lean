

theorem exists_dense_P3_superset {X} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ Dense B ∧ P3 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, dense_univ, ?_⟩
  simpa using (P3_of_open (A := (Set.univ : Set X)) isOpen_univ)

theorem P1_iff_P3_of_clopen {X} [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) : P1 A ↔ P3 A := by
  simpa using
    ((P1_iff_P2_of_open (A := A) hOpen).trans
      (P2_iff_P3_of_closed (A := A) hClosed))