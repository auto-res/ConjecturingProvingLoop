

theorem interior_nonempty_implies_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hIntA
  rcases hIntA with ⟨x, hxIntA⟩
  -- `interior A` is contained in `interior (closure A)` by monotonicity.
  have hMono :
      (interior (A : Set X) : Set X) ⊆
        interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  exact ⟨x, hMono hxIntA⟩