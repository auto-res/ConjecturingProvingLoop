

theorem Topology.closure_union_interior_compl_eq_univ {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  -- Rewrite `interior (Aᶜ)` in terms of the complement of `closure A`.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- The union of a set with its complement is the whole space.
  calc
    closure A ∪ interior (Aᶜ) = closure A ∪ (closure A)ᶜ := by
      simpa [h]
    _ = (Set.univ : Set X) := by
      simpa [Set.union_compl_self]