

theorem P3_iff_P2_closed_or_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed A ∨ IsOpen A) : P3 A ↔ P2 A := by
  classical
  cases h with
  | inl hClosed =>
      simpa using (P3_iff_P2_of_closed (A := A) hClosed)
  | inr hOpen =>
      simpa using ((P2_iff_P3_of_open (A := A) hOpen).symm)