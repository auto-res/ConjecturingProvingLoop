

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- `A` is contained in the interior of its closure since it is open.
  have hx' : x ∈ interior (closure A) := by
    have hsub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact hsub hx
  simpa [hA.interior_eq] using hx'

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P3 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsub : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hsub hx'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- We show that `interior (closure (interior A))` is contained in
      -- `interior (closure (interior (A ∪ B)))`.
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- First, relate the two closures.
        have h_closure :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- `interior A` is contained in `interior (A ∪ B)`
          -- because it is an open subset of `A ∪ B`.
          have h_int :
              (interior A : Set X) ⊆ interior (A ∪ B) := by
            have h_aux : (interior A : Set X) ⊆ (A ∪ B) := by
              intro y hy
              exact Or.inl (interior_subset hy)
            exact interior_maximal h_aux isOpen_interior
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      -- `x` comes from `B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      -- Similar containment for the `B` side.
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int :
              (interior B : Set X) ⊆ interior (A ∪ B) := by
            have h_aux : (interior B : Set X) ⊆ (A ∪ B) := by
              intro y hy
              exact Or.inr (interior_subset hy)
            exact interior_maximal h_aux isOpen_interior
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB'