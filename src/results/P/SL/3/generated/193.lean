

theorem closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (closure (interior (A : Set X))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro h_closure
    by_contra h_int
    have h_int_eq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp h_int
    have : (closure (∅ : Set X)).Nonempty := by
      simpa [h_int_eq] using h_closure
    simpa [closure_empty] using this
  · intro h_int
    rcases h_int with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩