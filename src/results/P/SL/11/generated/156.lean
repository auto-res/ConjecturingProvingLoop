

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro p hpAB
  rcases hpAB with ⟨hpA, hpB⟩
  -- Send each coordinate into the corresponding closure.
  have hclA : p.1 ∈ closure (interior A) := hA hpA
  have hclB : p.2 ∈ closure (interior B) := hB hpB
  -- Combine them to obtain membership in the product of closures.
  have hProd : p ∈ closure (interior A) ×ˢ closure (interior B) := ⟨hclA, hclB⟩
  -- Rewrite the goal using `closure_prod_eq`.
  have hProdIn :
      p ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [closure_prod_eq] using hProd
  -- Show that this closure is contained in the desired one.
  have hSubset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- First, establish the inclusion on the underlying sets.
    have hInnerSub :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      -- `interior A ×ˢ interior B` is open and contained in `A ×ˢ B`.
      have hOpen : IsOpen (interior A ×ˢ interior B) :=
        (isOpen_interior).prod isOpen_interior
      have hSub : (interior A ×ˢ interior B : Set _) ⊆ A ×ˢ B := by
        intro q hq
        exact ⟨(interior_subset hq.1), (interior_subset hq.2)⟩
      exact interior_maximal hSub hOpen
    -- Taking closures preserves inclusions.
    exact closure_mono hInnerSub
  exact hSubset hProdIn