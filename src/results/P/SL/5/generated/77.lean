

theorem interior_closure_eq_univ_iff_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) = Set.univ ↔ closure (A : Set X) = Set.univ := by
  constructor
  · intro hInt
    -- `univ ⊆ closure A`
    have h_univ_sub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      have hxInt : x ∈ interior (closure (A : Set X)) := by
        simpa [hInt] using hx
      exact interior_subset hxInt
    -- `closure A ⊆ univ` is trivial
    have h_closure_sub : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx
      trivial
    exact le_antisymm h_closure_sub h_univ_sub
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_closure_eq_univ
        (X := X) (A := A) hCl