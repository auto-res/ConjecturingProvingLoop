

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at *
  intro p hp
  -- Decompose `p` and obtain coordinate membership.
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P3` to each coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hpA
  have hIntB : p.2 ∈ interior (closure B) := hB hpB
  -- The point `p` lies in the product of the two interiors.
  have hMemProd :
      p ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨hIntA, hIntB⟩
  -- This rectangle is open.
  have hOpenProd :
      IsOpen (interior (closure A) ×ˢ interior (closure B)) :=
    (isOpen_interior).prod isOpen_interior
  -- Show the rectangle is contained in `closure (A ×ˢ B)`.
  have hSubProd :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A := (interior_subset) hqA
    have hqB_cl : q.2 ∈ closure B := (interior_subset) hqB
    have hqIn : q ∈ closure A ×ˢ closure B := ⟨hqA_cl, hqB_cl⟩
    simpa [closure_prod_eq] using hqIn
  -- Use `interior_maximal` to upgrade membership.
  have hSubInterior :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal hSubProd hOpenProd
  exact hSubInterior hMemProd