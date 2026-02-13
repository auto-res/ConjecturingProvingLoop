

theorem closure_interior_nonempty_iff_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  -- Translate the previously proved emptiness equivalence into a non‐emptiness equivalence.
  have hEmpty :
      closure (interior (A : Set X)) = (∅ : Set X) ↔
        interior (A : Set X) = (∅ : Set X) :=
    Topology.closure_interior_eq_empty_iff_interior_eq_empty
      (X := X) (A := A)
  simpa [Set.nonempty_iff_ne_empty] using not_congr hEmpty