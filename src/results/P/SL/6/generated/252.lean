

theorem P1_and_closure_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (interior (A : Set X)) = (∅ : Set X) → A = ∅ := by
  intro hP1 hClosEmpty
  -- `closure (interior A) = ∅` implies `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = ∅ :=
    ((closure_interior_eq_empty_iff (A := A)).1 hClosEmpty)
  -- Apply the existing lemma that uses the emptiness of `interior A`.
  exact
    Topology.P1_and_interior_empty_implies_empty
      (A := A) hP1 hIntEmpty