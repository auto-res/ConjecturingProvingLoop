

theorem Topology.closure_eq_univ_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro h
    simpa [h] using (isOpen_univ.interior_eq)
  · intro h
    -- `interior (closure A)` is contained in `closure A`.
    have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
      interior_subset
    -- Using `h`, this becomes `univ ⊆ closure A`.
    have h' : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [h] using hSub
    -- The reverse inclusion is trivial.
    have h'' : closure (A : Set X) ⊆ (Set.univ : Set X) := Set.Subset_univ _
    exact Set.Subset.antisymm h'' h'