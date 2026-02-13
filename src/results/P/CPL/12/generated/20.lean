

theorem P1_univ_iff {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P1_univ

theorem P3_univ_iff {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P3_univ