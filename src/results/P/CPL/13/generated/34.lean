

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∩ B) := by
  classical
  -- Unfold `P2`.
  dsimp [Topology.P2] at *
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Abbreviations.
  set U₁ : Set X := interior (closure (interior A)) with hU₁
  set U₂ : Set X := interior (closure (interior B)) with hU₂
  -- `x` belongs to both `U₁` and `U₂`.
  have hxU₁ : x ∈ U₁ := by
    simpa [hU₁] using hA hxA
  have hxU₂ : x ∈ U₂ := by
    simpa [hU₂] using hB hxB
  -- Define an open neighbourhood of `x`.
  let S : Set X := U₁ ∩ U₂
  have hS_open : IsOpen S := by
    simpa [hU₁, hU₂] using (isOpen_interior.inter isOpen_interior)
  have hxS : x ∈ S := And.intro hxU₁ hxU₂
  -- Main inclusion: `S ⊆ closure (interior (A ∩ B))`.
  have hS_subset :
      (S : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyU₁, hyU₂⟩
    -- `y` lies in the closures of the interiors of `A` and `B`.
    have hy_clA : y ∈ closure (interior A) := by
      have : y ∈ interior (closure (interior A)) := by
        simpa [hU₁] using hyU₁
      exact (interior_subset : interior (closure (interior A)) ⊆
                               closure (interior A)) this
    have hy_clB : y ∈ closure (interior B) := by
      have : y ∈ interior (closure (interior B)) := by
        simpa [hU₂] using hyU₂
      exact (interior_subset : interior (closure (interior B)) ⊆
                               closure (interior B)) this
    -- Show that every neighbourhood of `y` meets `interior (A ∩ B)`.
    refine (mem_closure_iff).2 ?_
    intro V hV hyV
    -- First step: intersect the neighbourhood with `U₂`.
    let W : Set X := V ∩ U₂
    have hW_open : IsOpen W := hV.inter (by
      simpa [hU₂] using isOpen_interior)
    have hyW : y ∈ W := ⟨hyV, hyU₂⟩
    -- `W` meets `interior A`.
    have h_nonempty₁ :
        (W ∩ interior A).Nonempty := by
      have h_cl := (mem_closure_iff).1 hy_clA
      exact h_cl W hW_open hyW
    rcases h_nonempty₁ with ⟨z, hz⟩
    -- Decompose the information on `z`.
    have hzV      : z ∈ V := hz.1.1
    have hzU₂     : z ∈ U₂ := hz.1.2
    have hz_intA  : z ∈ interior A := hz.2
    -- From `hzU₂` we obtain `z ∈ closure (interior B)`.
    have hz_clB : z ∈ closure (interior B) := by
      have : z ∈ interior (closure (interior B)) := by
        simpa [hU₂] using hzU₂
      exact (interior_subset : interior (closure (interior B)) ⊆
                               closure (interior B)) this
    -- Second step: intersect the neighbourhood with `interior A`.
    let V₂ : Set X := V ∩ interior A
    have hV₂_open : IsOpen V₂ := hV.inter isOpen_interior
    have hzV₂ : z ∈ V₂ := ⟨hzV, hz_intA⟩
    -- `V₂` meets `interior B`.
    have h_nonempty₂ : (V₂ ∩ interior B).Nonempty := by
      have h_cl := (mem_closure_iff).1 hz_clB
      exact h_cl V₂ hV₂_open hzV₂
    rcases h_nonempty₂ with ⟨w, hw⟩
    -- Extract the required memberships for `w`.
    have hwV      : w ∈ V := hw.1.1
    have hw_intA  : w ∈ interior A := hw.1.2
    have hw_intB  : w ∈ interior B := hw.2
    -- Hence `w` lies in `interior (A ∩ B)`.
    have hw_intAB : w ∈ interior (A ∩ B) := by
      -- `interior (A ∩ B) = interior A ∩ interior B`.
      have : w ∈ interior A ∩ interior B := ⟨hw_intA, hw_intB⟩
      simpa [interior_inter] using this
    -- Provide the witness required by `mem_closure_iff`.
    exact ⟨w, hwV, hw_intAB⟩
  -- Using maximality of the interior.
  have hS_subset_int :
      (S : Set X) ⊆ interior (closure (interior (A ∩ B))) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`.
  exact hS_subset_int hxS

theorem P3_of_interior_closure_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior (closure A)) = Set.univ) : Topology.P3 A := by
  -- First, show that `closure A = Set.univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := by
    -- `closure (interior (closure A)) ⊆ closure A`.
    have h_sub : closure (interior (closure A)) ⊆ closure A := by
      -- This follows from monotonicity of `closure` applied to
      -- `interior_subset : interior (closure A) ⊆ closure A`.
      simpa [closure_closure] using
        closure_mono
          (interior_subset : interior (closure A) ⊆ closure A)
    -- Rewrite the left‐hand side using the hypothesis `h`.
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [h] using h_sub
    -- Combine the two inclusions to obtain the equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Consequently, `interior (closure A) = Set.univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- Finish the proof of `P3 A`.
  dsimp [Topology.P3]
  intro x hxA
  -- With the preceding equality, the desired membership is immediate.
  simpa [h_int_univ] using (Set.mem_univ x)

theorem P1_of_dense_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ closure (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1] at *
  exact Set.Subset.trans subset_closure h