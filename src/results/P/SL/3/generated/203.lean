

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty →
      Topology.P1 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP1
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntA : (interior (A : Set X)).Nonempty :=
    interior_nonempty_of_P1 (A := A) hA hP1
  rcases hIntA with ⟨x, hx_intA⟩
  -- `interior A` is contained in `interior (closure A)`.
  have hx_intCl : (x : X) ∈ interior (closure (A : Set X)) := by
    have h_subset :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_subset_interior_closure (A := A)
    exact h_subset hx_intA
  exact ⟨x, hx_intCl⟩