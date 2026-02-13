

theorem Topology.nonempty_closureInterior_iff_nonempty_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro h_nonempty_cl
    -- `closure (interior A)` is not empty.
    have h_cl_ne : closure (interior (A : Set X)) ≠ (∅ : Set X) :=
      (Set.nonempty_iff_ne_empty).1 h_nonempty_cl
    -- If `interior A` were empty, the equivalence would force its closure to be empty,
    -- contradicting `h_cl_ne`.
    have h_int_ne : interior (A : Set X) ≠ (∅ : Set X) := by
      intro h_int_eq
      have h_cl_eq : closure (interior (A : Set X)) = (∅ : Set X) :=
        ((Topology.closureInterior_eq_empty_iff (X := X) (A := A)).2 h_int_eq)
      exact h_cl_ne h_cl_eq
    exact (Set.nonempty_iff_ne_empty).2 h_int_ne
  · intro h_nonempty_int
    rcases h_nonempty_int with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩