

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- unpack the hypothesis and the goal
  dsimp [Topology.P3] at hA ⊢
  intro y hy
  -- write `y` as `e x` with `x ∈ A`
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the hypothesis on `A`
  have hx : x ∈ interior (closure (A : Set X)) := hA hxA
  -- `e x` belongs to the image of this interior
  have h_mem : (e : X → Y) x ∈ e '' interior (closure (A : Set X)) :=
    ⟨x, hx, rfl⟩
  -- this image is open, since `e` is an open map
  have h_open : IsOpen (e '' interior (closure (A : Set X))) :=
    (e.isOpenMap) _ isOpen_interior
  -- and it is contained in the closure of `e '' A`
  have h_subset :
      (e '' interior (closure (A : Set X))) ⊆ closure (e '' A) := by
    intro y hy
    rcases hy with ⟨x', hx', rfl⟩
    have hx'_cl : x' ∈ closure (A : Set X) := interior_subset hx'
    have h_in : (e : X → Y) x' ∈ e '' closure (A : Set X) :=
      ⟨x', hx'_cl, rfl⟩
    have h_eq : e '' closure (A : Set X) = closure (e '' A) := by
      simpa using e.image_closure (s := A)
    simpa [h_eq] using h_in
  -- therefore it is contained in the interior of that closure
  have h_subset' :
      (e '' interior (closure (A : Set X))) ⊆
        interior (closure (e '' A)) :=
    interior_maximal h_subset h_open
  -- conclude for our point
  exact h_subset' h_mem

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e.symm '' B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hB ⊢
  -- Take a point `x` of the set `e.symm '' B`.
  intro x hx
  -- Write it as the image of a point `y ∈ B`.
  rcases hx with ⟨y, hyB, rfl⟩
  -- Apply the hypothesis `hB`.
  have hy : y ∈ interior (closure (interior (B : Set Y))) := hB hyB
  -- Consider the open set
  --   W = e.symm '' interior (closure (interior B)).
  have hW_open :
      IsOpen (e.symm '' interior (closure (interior (B : Set Y)))) :=
    (e.symm.isOpenMap) _ isOpen_interior
  -- The point belongs to `W`.
  have hxW :
      e.symm y ∈ e.symm '' interior (closure (interior (B : Set Y))) :=
    ⟨y, hy, rfl⟩
  -- We claim that `W` is contained in the closure of
  -- `interior (e.symm '' B)`.
  have hW_sub :
      (e.symm '' interior (closure (interior (B : Set Y)))) ⊆
        closure (interior (e.symm '' B)) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    -- `w ∈ interior (closure (interior B))` implies
    -- `w ∈ closure (interior B)`.
    have hw_cl : w ∈ closure (interior (B : Set Y)) :=
      interior_subset hw
    -- Use the behaviour of `closure` under a homeomorphism.
    have h_cl_eq :
        (e.symm '' closure (interior (B : Set Y))) =
          closure (e.symm '' interior (B : Set Y)) := by
      simpa using (e.symm.image_closure (s := interior (B : Set Y)))
    have hz₁ :
        e.symm w ∈ closure (e.symm '' interior (B : Set Y)) := by
      have : e.symm w ∈ e.symm '' closure (interior (B : Set Y)) :=
        ⟨w, hw_cl, rfl⟩
      simpa [h_cl_eq] using this
    -- Show that `e.symm '' interior B ⊆ interior (e.symm '' B)`.
    have h_int_in :
        (e.symm '' interior (B : Set Y)) ⊆ interior (e.symm '' B) := by
      have h_sub :
          (e.symm '' interior (B : Set Y)) ⊆ e.symm '' B := by
        intro u hu
        rcases hu with ⟨w', hw'int, rfl⟩
        exact ⟨w', interior_subset hw'int, rfl⟩
      have h_open' :
          IsOpen (e.symm '' interior (B : Set Y)) :=
        (e.symm.isOpenMap) _ isOpen_interior
      exact interior_maximal h_sub h_open'
    -- Pass to closures.
    have h_cl_mono :
        closure (e.symm '' interior (B : Set Y)) ⊆
          closure (interior (e.symm '' B)) :=
      closure_mono h_int_in
    exact h_cl_mono hz₁
  -- Since `W` is open and contained in the closure, it is contained in its interior.
  have hW_sub_int :
      (e.symm '' interior (closure (interior (B : Set Y)))) ⊆
        interior (closure (interior (e.symm '' B))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  classical
  -- `A` is nonempty since it contains `x`, hence it is the whole space.
  have hAuniv : (A : Set X) = (Set.univ : Set X) := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have hz : z = x := Subsingleton.elim z x
      simpa [hz] using hx
  -- Rewrite the goal using this fact.
  simpa [hAuniv, closure_univ, interior_univ]

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 (closure A) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3]
  -- First, prove that `closure A = univ`.
  have h_closure_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- From the density hypothesis we have `closure (interior A) = univ`.
    have h1 : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      simpa using h.closure_eq
    -- And clearly `closure (interior A) ⊆ closure A`.
    have h2 : closure (interior (A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`.
    have h3 : (Set.univ : Set X) ⊆ closure A := by
      simpa [h1] using h2
    -- Combine the two inclusions to get equality.
    exact subset_antisymm (Set.subset_univ _) h3
  -- Now establish the required inclusion.
  intro x hx
  -- After rewriting, the goal is trivial.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, h_closure_univ, interior_univ] using this

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point `x` in `A \ B`.
  intro x hx
  rcases hx with ⟨hxA, hx_notB⟩
  -- Apply the hypothesis on `A`.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  /-  Work with the open set
        V = interior (closure (interior A)) \ B. -/
  have hV_open : IsOpen (interior (closure (interior A)) \ B) := by
    --  `V` is the intersection of two open sets.
    have h1 : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h2 : IsOpen (Bᶜ) := hB.isOpen_compl
    simpa [Set.diff_eq] using h1.inter h2
  have hxV : x ∈ interior (closure (interior A)) \ B :=
    ⟨hx_int, hx_notB⟩
  -- Main inclusion: `V ⊆ closure (interior (A \ B))`.
  have hV_sub :
      (interior (closure (interior A)) \ B : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- From `hy_int` we deduce that `y` is in the closure of `interior A`.
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- We now prove that `y` is in the closure of `interior (A \ B)`.
    have : y ∈ closure (interior (A \ B)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Shrink the neighbourhood to avoid `B`.
      have hW_diff_open : IsOpen (W \ B) := by
        have h_open_compl : IsOpen (Bᶜ) := hB.isOpen_compl
        simpa [Set.diff_eq] using hW_open.inter h_open_compl
      have hyWdiff : y ∈ W \ B := by
        exact ⟨hyW, hy_notB⟩
      -- Since `y` is in the closure of `interior A`, this set meets `interior A`.
      have h_nonempty :
          ((W \ B) ∩ interior A).Nonempty := by
        have h_prop := (mem_closure_iff).1 hy_cl
        exact h_prop (W \ B) hW_diff_open hyWdiff
      -- Pick a point `z` in the intersection.
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨hzWdiff, hz_intA⟩
      rcases hzWdiff with ⟨hzW, hz_notB⟩
      -- `z` belongs to `interior A \ B`.
      have hz_intA_notB : z ∈ interior A \ B := ⟨hz_intA, hz_notB⟩
      -- Show that `interior A \ B ⊆ interior (A \ B)`.
      have h_int_subset :
          (interior A \ B : Set X) ⊆ interior (A \ B) := by
        -- `interior A \ B` is open and contained in `A \ B`.
        have h_open_int_diff : IsOpen (interior A \ B) := by
          have h_open_compl : IsOpen (Bᶜ) := hB.isOpen_compl
          simpa [Set.diff_eq] using (isOpen_interior).inter h_open_compl
        have h_sub : (interior A \ B : Set X) ⊆ A \ B := by
          intro t ht
          rcases ht with ⟨ht_intA, ht_notB⟩
          exact ⟨interior_subset ht_intA, ht_notB⟩
        exact interior_maximal h_sub h_open_int_diff
      -- Hence `z ∈ interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) :=
        h_int_subset hz_intA_notB
      -- Provide the required witness in `W ∩ interior (A \ B)`.
      exact ⟨z, ⟨hzW, hz_int_diff⟩⟩
    exact this
  -- Since `V` is open and contained in the closure, it is contained in its interior.
  have hV_sub_int :
      (interior (closure (interior A)) \ B : Set X) ⊆
        interior (closure (interior (A \ B))) :=
    interior_maximal hV_sub hV_open
  -- Conclude for the original point `x`.
  exact hV_sub_int hxV