

theorem Topology.not_P3_of_nonempty_emptyInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : A.Nonempty)
    (hIntEmpty : interior (closure A) = (∅ : Set X)) :
    ¬ Topology.P3 (X := X) A := by
  intro hP3
  -- From `P3` and the hypothesis on the interior we deduce `A = ∅`.
  have hAempty :
      A = (∅ : Set X) :=
    Topology.P3_emptyInteriorClosure_implies_empty
      (X := X) (A := A) hP3 hIntEmpty
  -- But `A` was assumed nonempty—contradiction.
  have hNonemptyEmpty : (∅ : Set X).Nonempty := by
    simpa [hAempty] using hA
  cases hNonemptyEmpty with
  | intro x hx =>
      cases hx