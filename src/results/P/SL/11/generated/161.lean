

theorem P3_prod_right_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro p hpAB
  -- Decompose the point `p` into its coordinates.
  rcases hpAB with ⟨hpA, hpB⟩
  -- Apply `P3` to the first coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hpA
  -- Form an open rectangle containing `p`.
  have hMem : p ∈ interior (closure A) ×ˢ B := ⟨hIntA, hpB⟩
  have hOpen : IsOpen (interior (closure A) ×ˢ B) :=
    (isOpen_interior).prod hB_open
  -- Show that the rectangle is contained in `closure (A ×ˢ B)`.
  have hSub :
      (interior (closure A) ×ˢ B : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hqA
    have hqB_cl : q.2 ∈ closure B := subset_closure hqB
    have : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using this
  -- Upgrade membership to the desired interior via `interior_maximal`.
  have hSubInt :
      (interior (closure A) ×ˢ B : Set _) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hSub hOpen
  exact hSubInt hMem