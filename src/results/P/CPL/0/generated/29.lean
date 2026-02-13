

theorem P1_iff_interior_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ interior A ∪ closure (interior A) = closure A := by
  classical
  constructor
  · intro hP1
    -- `h_eq` is the equality of closures coming from `P1`
    have h_eq : closure (interior A) = closure A :=
      (P1_iff_closure_inter_eq).1 hP1
    -- `interior A` is contained in `closure (interior A)`
    have h_union : interior A ∪ closure (interior A) = closure (interior A) :=
      (Set.union_eq_right.2
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
    -- put the two equalities together
    simpa [h_union] using h_eq
  · intro hUnion
    -- first inclusion: `closure (interior A) ⊆ closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- second inclusion: `closure A ⊆ closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      intro x hx
      -- rewrite membership using `hUnion`
      have hx_union : x ∈ interior A ∪ closure (interior A) := by
        simpa [hUnion] using hx
      cases hx_union with
      | inl hInt => exact subset_closure hInt
      | inr hCl  => exact hCl
    -- deduce equality of closures
    have h_eq : closure (interior A) = closure A :=
      Set.Subset.antisymm h₁ h₂
    -- conclude `P1 A`
    exact (P1_iff_closure_inter_eq).2 h_eq