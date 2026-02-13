

theorem P1_of_dense_set {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P1 (closure A) := by
  -- `A` is dense, hence its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  -- Rewrite and conclude using `P1_univ`.
  simpa [hclosure] using (P1_univ (X := X))

theorem P2_image_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (f '' A) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point in the image.
  intro y hy
  -- Write it as `f x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis on `A`.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  -- Define the auxiliary open set
  --   W = f '' interior (closure (interior A)).
  set W : Set Y := f '' interior (closure (interior (A : Set X))) with hWdef
  -- This set is open, as `f` is an open map.
  have hW_open : IsOpen W := by
    have : IsOpen (interior (closure (interior (A : Set X)))) :=
      isOpen_interior
    simpa [hWdef] using h_open _ this
  -- The point `f x` belongs to `W`.
  have hxW : f x ∈ W := by
    refine ⟨x, hx, rfl⟩
  -- We will show that `W ⊆ closure (interior (f '' A))`.
  have hW_sub_cl :
      W ⊆ closure (interior (f '' (A : Set X))) := by
    intro z hz
    -- Write `z = f x'` with `x' ∈ interior (closure (interior A))`.
    rcases (show ∃ x', x' ∈ interior (closure (interior (A : Set X))) ∧ f x' = z from by
        rcases hz with ⟨x', hx', rfl⟩
        exact ⟨x', hx', rfl⟩) with ⟨x', hx', rfl⟩
    -- From `hx'` we get `x' ∈ closure (interior A)`.
    have hx'cl : x' ∈ closure (interior (A : Set X)) :=
      interior_subset hx'
    -- We prove `f x' ∈ closure (interior (f '' A))`
    -- using the neighborhood characterization of the closure.
    have : f x' ∈ closure (interior (f '' (A : Set X))) := by
      -- Reformulate with `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro V hV_open hfxV
      -- Pull back the neighborhood `V` through `f`.
      have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
      have hx'U : x' ∈ f ⁻¹' V := hfxV
      -- Since `x'` is in the closure of `interior A`, the intersection
      --   (f ⁻¹ V) ∩ interior A
      -- is non‐empty.
      have h_nonempty :
          ((f ⁻¹' V) ∩ interior (A : Set X)).Nonempty := by
        have h_cl := (mem_closure_iff).1 hx'cl
        exact h_cl _ hU_open hx'U
      rcases h_nonempty with ⟨w, hwU, hw_intA⟩
      -- The point `f w` is in `V` and also in the image of `interior A`.
      have hfwV : f w ∈ V := hwU
      -- `f w` lies in `f '' interior A`, which is open.
      have h_open_im : IsOpen (f '' interior (A : Set X)) :=
        h_open _ isOpen_interior
      -- Show that `f '' interior A ⊆ interior (f '' A)`.
      have h_im_sub_int :
          (f '' interior (A : Set X)) ⊆ interior (f '' (A : Set X)) :=
        interior_maximal
          (by
            intro t ht
            rcases ht with ⟨u, hu_intA, rfl⟩
            exact ⟨u, interior_subset hu_intA, rfl⟩)
          h_open_im
      -- Hence `f w ∈ interior (f '' A)`.
      have hfw_int : f w ∈ interior (f '' (A : Set X)) :=
        h_im_sub_int ⟨w, hw_intA, rfl⟩
      -- Provide the required witness in `V ∩ interior (f '' A)`.
      exact ⟨f w, hfwV, hfw_int⟩
    simpa using this
  -- Since `W` is open and contained in the closure, it is contained
  -- in the interior of that closure.
  have hW_sub_int :
      W ⊆ interior (closure (interior (f '' (A : Set X)))) :=
    interior_maximal hW_sub_cl hW_open
  -- Apply this inclusion to the point `f x`.
  exact hW_sub_int (by
    simpa [hWdef] using hxW)

theorem P3_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (closure (A ∪ Set.univ)) := by
  simpa [Set.union_univ, closure_univ] using (P3_univ (X := X))

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P3 (A 0)) (hstep : ∀ n, Topology.P3 (A n) → Topology.P3 (A (n+1))) : ∀ n, Topology.P3 (A n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => exact hstep n ih