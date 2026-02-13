

theorem P3_inter_of_P3_and_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3 : Topology.P3 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `A`, place `x` inside `interior (closure A)`.
  have hxIntA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Consider the open neighbourhood `V = interior (closure A) ∩ B` of `x`.
  let V : Set X := interior (closure (A : Set X)) ∩ B
  have hV_open : IsOpen V := isOpen_interior.inter hOpenB
  have hxV     : x ∈ V := by
    dsimp [V]
    exact And.intro hxIntA hxB
  -- We claim that `V ⊆ closure (A ∩ B)`.
  have hV_sub : (V : Set X) ⊆ closure (A ∩ B) := by
    intro y hyV
    rcases hyV with ⟨hyIntA, hyB⟩
    -- `y` lies in `closure A`.
    have hyClA : y ∈ closure (A : Set X) :=
      (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hyIntA
    -- Show `y ∈ closure (A ∩ B)` using the neighbourhood criterion.
    have : y ∈ closure (A ∩ B : Set X) := by
      -- Reformulate with `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro U hU hyU
      -- Intersect the given neighbourhood with `B`, which is open and contains `y`.
      have hU' : IsOpen (U ∩ B) := hU.inter hOpenB
      have hyU' : y ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure A`, this new neighbourhood meets `A`.
      have hNon : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU' hyU'
      -- Extract a witness in `U ∩ (A ∩ B)`.
      rcases hNon with ⟨z, ⟨hzU, hzB⟩, hzA⟩
      exact ⟨z, And.intro hzU (And.intro hzA hzB)⟩
    exact this
  -- Conclude that `x ∈ interior (closure (A ∩ B))`.
  exact (interior_maximal hV_sub hV_open) hxV