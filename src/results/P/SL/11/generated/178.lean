

theorem closure_interior_prod_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior A) ×ˢ closure (interior B) ⊆
      closure (interior (A ×ˢ B)) := by
  intro p hp
  -- Step 1: rewrite the hypothesis using `closure_prod_eq`.
  have h₁ : (p : X × Y) ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [closure_prod_eq] using hp
  -- Step 2: show the needed containment between the closures.
  have hsubset :
      (closure ((interior A) ×ˢ (interior B)) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    apply closure_mono
    -- Establish the inclusion on the underlying sets via `interior_maximal`.
    have hInnerSub :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      -- `interior A ×ˢ interior B` is an open subset of `A ×ˢ B`.
      have hOpen : IsOpen (interior A ×ˢ interior B) :=
        (isOpen_interior).prod isOpen_interior
      have hSub : (interior A ×ˢ interior B : Set _) ⊆ A ×ˢ B := by
        intro q hq
        exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
      exact interior_maximal hSub hOpen
    exact hInnerSub
  -- Step 3: conclude by applying the inclusion to the membership obtained in Step 1.
  exact hsubset h₁