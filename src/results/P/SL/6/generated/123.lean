

theorem nonempty_interior_closure_of_nonempty_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP1 hNon
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntNon : (interior (A : Set X)).Nonempty :=
    nonempty_interior_of_nonempty_P1 (A := A) hP1 hNon
  rcases hIntNon with ⟨x, hxIntA⟩
  -- `interior A` is contained in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩