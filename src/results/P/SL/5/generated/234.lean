

theorem interior_closure_interior_nonempty_iff_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (interior (closure (interior (A : Set X)))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    -- From a point in the interior we obtain one in the closure.
    have hCl : (closure (interior (A : Set X))).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, interior_subset hx⟩
    -- Use an existing lemma to deduce non‐emptiness of `A`.
    exact
      Topology.nonempty_of_closure_interior_nonempty
        (X := X) (A := A) hCl
  · intro hA
    -- Apply the forward implication already available for `P2`.
    exact
      Topology.interior_closure_interior_nonempty_of_P2
        (X := X) (A := A) hP2 hA