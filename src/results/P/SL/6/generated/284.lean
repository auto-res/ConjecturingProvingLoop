

theorem P1_inter_of_P1_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `closure (interior A)` thanks to `P1` for `A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- We prove `x ∈ closure (interior (A ∩ B))` via the neighborhood
  -- characterization of the closure.
  apply (mem_closure_iff).2
  intro U hU hxU
  -- Intersect the given neighborhood with `B`, which is open and contains `x`.
  have hV_open : IsOpen (U ∩ B) := hU.inter hOpenB
  have hxV    : x ∈ U ∩ B       := And.intro hxU hxB
  -- Since `x ∈ closure (interior A)`, this new neighborhood meets `interior A`.
  have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
    ((mem_closure_iff).1 hx_clA) (U ∩ B) hV_open hxV
  rcases hNon with ⟨y, ⟨hyU, hyB⟩, hyIntA⟩
  -- We will show that such a point `y` actually belongs to
  -- `interior (A ∩ B)` and, hence, to the required intersection.
  have hyIntAB : y ∈ interior (A ∩ B) := by
    -- `y` lies in `interior A ∩ B`.
    have hyIn : y ∈ (interior (A : Set X)) ∩ B := And.intro hyIntA hyB
    -- The set `interior A ∩ B` is open and contained in `A ∩ B`,
    -- so it sits inside `interior (A ∩ B)`.
    have hSub :
        ((interior (A : Set X)) ∩ B : Set X) ⊆ interior (A ∩ B) := by
      have hOpen : IsOpen ((interior (A : Set X)) ∩ B : Set X) :=
        (isOpen_interior).inter hOpenB
      have hIncl :
          ((interior (A : Set X)) ∩ B : Set X) ⊆ (A ∩ B) := by
        intro z hz
        exact And.intro
          ((interior_subset : interior (A : Set X) ⊆ A) hz.1) hz.2
      exact interior_maximal hIncl hOpen
    exact hSub hyIn
  -- Assemble the witness of non-emptiness required by `mem_closure_iff`.
  exact ⟨y, And.intro hyU hyIntAB⟩