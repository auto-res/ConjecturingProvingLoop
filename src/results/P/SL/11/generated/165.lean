

theorem P3_prod_left_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hB ⊢
  intro p hpAB
  rcases hpAB with ⟨hpA, hpB⟩
  -- Apply `P3` to obtain interior membership for the second coordinate.
  have hIntB : p.2 ∈ interior (closure B) := hB hpB
  -- Form an open rectangle `A ×ˢ interior (closure B)` containing `p`.
  have hMem : p ∈ A ×ˢ interior (closure B) := ⟨hpA, hIntB⟩
  have hOpenRect : IsOpen (A ×ˢ interior (closure B)) :=
    hA_open.prod isOpen_interior
  -- Show that this rectangle is contained in `closure (A ×ˢ B)`.
  have hSub : (A ×ˢ interior (closure B) : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqBInt⟩
    have hqA_cl : q.1 ∈ closure A := subset_closure hqA
    have hqB_cl : q.2 ∈ closure B :=
      (interior_subset : interior (closure B) ⊆ closure B) hqBInt
    have : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using this
  -- Use `interior_maximal` to upgrade to interior membership.
  have hSubInt :
      (A ×ˢ interior (closure B) : Set _) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal hSub hOpenRect
  exact hSubInt hMem