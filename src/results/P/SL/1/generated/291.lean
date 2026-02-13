

theorem Topology.interior_inter_open_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    -- `x` belongs to `A ∩ B`
    have hxAB : x ∈ A ∩ B :=
      (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
    -- Extract the individual facts
    have hxA : x ∈ A := hxAB.1
    -- Monotonicity of `interior` yields `x ∈ interior B`
    have hxIntB : x ∈ interior B := by
      have hsubset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hsubset) hx
    exact And.intro hxA hxIntB
  · -- `⊇` direction
    intro x hx
    -- Separate the hypotheses
    have hxA : x ∈ A := hx.1
    have hxIntB : x ∈ interior B := hx.2
    -- Basic facts about `interior B`
    have hOpenIntB : IsOpen (interior B) := isOpen_interior
    have hIntSubsetB : (interior B : Set X) ⊆ B := interior_subset
    -- Consider the open set `V = interior B ∩ A`
    have hVopen : IsOpen ((interior B) ∩ A) := hOpenIntB.inter hA
    have hxV : x ∈ (interior B) ∩ A :=
      And.intro hxIntB hxA
    -- `V` is contained in `A ∩ B`
    have hVsubset : ((interior B) ∩ A : Set X) ⊆ A ∩ B := by
      intro y hy
      have hyIntB : y ∈ interior B := hy.1
      have hyA    : y ∈ A := hy.2
      have hyB    : y ∈ B := hIntSubsetB hyIntB
      exact And.intro hyA hyB
    -- Hence `x` is in the interior of `A ∩ B`
    have : x ∈ interior (A ∩ B) := by
      -- `interior_maximal` turns the inclusion of the open set `V`
      -- into an inclusion in the interior.
      have hsubsetInt : ((interior B) ∩ A : Set X) ⊆ interior (A ∩ B) := by
        apply interior_maximal hVsubset hVopen
      exact hsubsetInt hxV
    exact this