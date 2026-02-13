

theorem Topology.closure_eq_univ_iff_interior_compl_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) ↔ interior (Aᶜ) = (∅ : Set X) := by
  -- Useful relations between `closure` and `interior` for complements.
  have h₁ := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  have h₂ := Topology.closure_eq_compl_interior_compl (X := X) (A := A)
  constructor
  · intro hCl
    -- Rewrite `h₁` using `hCl` to eliminate `closure A`.
    have : interior (Aᶜ) = (Set.univ : Set X)ᶜ := by
      simpa [hCl] using h₁
    -- The complement of `univ` is `∅`.
    simpa [Set.compl_univ] using this
  · intro hInt
    -- Rewrite `h₂` using `hInt` to eliminate `interior (Aᶜ)`.
    have : closure A = (∅ : Set X)ᶜ := by
      simpa [hInt] using h₂
    -- The complement of `∅` is `univ`.
    simpa [Set.compl_empty] using this