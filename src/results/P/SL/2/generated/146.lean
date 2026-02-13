

theorem Topology.interior_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  apply subset_antisymm
  · -- `⊆` direction: from left to right
    intro x hx
    -- A point in `interior (A ∩ B)` lies in `A ∩ B`
    have hxAB : x ∈ (A ∩ B : Set X) := interior_subset hx
    -- Hence it lies in `A`
    have hxA : x ∈ A := hxAB.1
    -- And, since `A ∩ B ⊆ B`, it also lies in `interior B`
    have hSub : (A ∩ B : Set X) ⊆ (B : Set X) := by
      intro y hy; exact hy.2
    have hxIntB : x ∈ interior (B : Set X) := (interior_mono hSub) hx
    exact And.intro hxA hxIntB
  · -- `⊇` direction: from right to left
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- `A ∩ interior B` is an open neighbourhood of `x`
    have hOpen : IsOpen (A ∩ interior (B : Set X) : Set X) :=
      hA.inter isOpen_interior
    -- and is contained in `A ∩ B`
    have hSub : (A ∩ interior (B : Set X) : Set X) ⊆ (A ∩ B : Set X) := by
      intro y hy
      have hyB : y ∈ B := interior_subset hy.2
      exact And.intro hy.1 hyB
    -- Therefore, by maximality of the interior, it is contained in `interior (A ∩ B)`
    have hIncl : (A ∩ interior (B : Set X) : Set X) ⊆
        interior (A ∩ B : Set X) := interior_maximal hSub hOpen
    -- Since `x` lies in `A ∩ interior B`, it also lies in the interior of `A ∩ B`
    have : x ∈ (A ∩ interior (B : Set X) : Set X) := And.intro hxA hxIntB
    exact hIncl this