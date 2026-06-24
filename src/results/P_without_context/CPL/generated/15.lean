

theorem P2_implies_P1 (A : Set X) : P2 A → P1 A := by
  intro h
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
      (h hx)

theorem P2_implies_P3 (A : Set X) : P2 A → P3 A := by
  intro h
  intro x hx
  exact
    (interior_mono
        (closure_mono (interior_subset : (interior A) ⊆ A)))
      (h hx)

theorem closure_eq_of_P1 (A : Set X) (h : P1 A) : closure (interior A) = closure A := by
  apply subset_antisymm
  · exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hA hxA
      have h_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inl hy)
      exact (closure_mono h_subset) hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hB hxB
      have h_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inr hy)
      exact (closure_mono h_subset) hx_closure

theorem P1_iff_dense_interior (A : Set X) : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro h
    exact closure_eq_of_P1 A h
  · intro h_eq
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq.symm] using this