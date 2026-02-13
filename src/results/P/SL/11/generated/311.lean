

theorem closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    (closure (interior A)).Nonempty ↔ A.Nonempty := by
  have h₁ :
      (closure (interior A)).Nonempty ↔ (interior A).Nonempty :=
    (closure_interior_nonempty_iff_interior_nonempty (A := A))
  have h₂ : (interior A).Nonempty ↔ A.Nonempty :=
    (interior_nonempty_iff_nonempty_of_P2 (A := A) hP2)
  simpa using h₁.trans h₂