

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hAne
  -- First, show that `interior A` is nonempty.
  have hInt_nonempty : (interior A).Nonempty := by
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hIntEmpty
    -- From `P1` and the emptiness of `interior A`, deduce `A = ∅`, contradiction.
    have hAEq : (A : Set X) = (∅ : Set X) :=
      Topology.P1_imp_eq_empty_of_empty_interior
        (X := X) (A := A) hP1 hIntEq
    rcases hAne with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hAEq] using hx
    exact this.elim
  -- Pick a point of `interior A`.
  rcases hInt_nonempty with ⟨x, hxInt⟩
  -- `interior A ⊆ interior (closure A)` by monotonicity.
  have hSubset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  exact ⟨x, hSubset hxInt⟩