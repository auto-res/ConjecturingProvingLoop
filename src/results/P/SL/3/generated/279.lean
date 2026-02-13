

theorem closure_eq_univ_of_empty_interior_complement
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hIntEmpty : interior ((Aᶜ) : Set X) = (∅ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  classical
  -- Relate the complement of `closure A` to `interior (Aᶜ)`.
  have hEq : (closure (A : Set X))ᶜ = interior ((Aᶜ) : Set X) :=
    (interior_complement_eq_complement_closure (A := A)).symm
  -- Deduce that the complement of `closure A` is empty.
  have hCompl : (closure (A : Set X))ᶜ = (∅ : Set X) := by
    simpa [hIntEmpty] using hEq
  -- Show that `closure A` contains every point of the space.
  have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    intro x _
    by_contra hx
    have hxInCompl : (x : X) ∈ (closure (A : Set X))ᶜ := hx
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hCompl] using hxInCompl
    exact this.elim
  -- Conclude the desired equality.
  exact Set.Subset.antisymm (Set.subset_univ _) hSub