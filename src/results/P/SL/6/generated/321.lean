

theorem P1_inter_of_P1_and_open_fixed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- Unpack the definition of `P1` for `A` and the goal.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `closure (interior A)` thanks to `P1 A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- We will prove that `x ∈ closure (interior (A ∩ B))`
  -- using the neighbourhood‐characterisation of the closure.
  have hx_cl : x ∈ closure (interior (A ∩ B)) := by
    -- Reformulate `closure` membership via `mem_closure_iff`.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Intersect the given neighbourhood with `B`, which is open and contains `x`.
    have hV_open : IsOpen (U ∩ B) := hU.inter hOpenB
    have hxV     : x ∈ U ∩ B       := And.intro hxU hxB
    -- Since `x ∈ closure (interior A)`, this new neighbourhood meets `interior A`.
    have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ B) hV_open hxV
    -- Extract a witness `y`.
    rcases hNon with ⟨y, ⟨⟨hyU, hyB⟩, hyIntA⟩⟩
    -- `y` lies in `interior A ∩ B`, hence in `interior (A ∩ B)`
    -- because `B` is open.
    have hyIntAB : y ∈ interior (A ∩ B) := by
      have hEq :=
        (interior_inter_of_isOpen_right (A := A) (B := B) hOpenB)
      have : y ∈ interior A ∩ B := And.intro hyIntA hyB
      simpa [hEq] using this
    -- Provide the required witness inside `U ∩ interior (A ∩ B)`.
    exact ⟨y, And.intro hyU hyIntAB⟩
  -- Conclude the goal.
  exact hx_cl