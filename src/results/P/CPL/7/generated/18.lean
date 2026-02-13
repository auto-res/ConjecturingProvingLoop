

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  intro x hx
  -- First, view `hx` as a membership in `interior (interior A)`.
  have hx₁ : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  -- `interior (interior A)` is included in `interior (closure (interior A))`.
  have h_subset :
      interior (interior A) ⊆ interior (closure (interior A)) := by
    have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_mono this
  -- Apply this inclusion.
  have hx₂ : x ∈ interior (closure (interior A)) := h_subset hx₁
  -- Re-express the target set via `interior_interior`.
  simpa [interior_interior] using hx₂

theorem P3_image_of_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : IsOpenMap f) (hcont : Continuous f) : Topology.P3 A → Topology.P3 (f '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of `closure A`
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Define `U := interior (closure A)`
  let U : Set X := interior (closure (A : Set X))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior
  have hxU : x ∈ U := by
    dsimp [U] at *
    simpa using hx_int
  -- Define `V := f '' U`
  let V : Set Y := f '' U
  have hV_open : IsOpen V := by
    dsimp [V]
    exact hf _ hU_open
  have hyV : (f x) ∈ V := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  ------------------------------------------------------------------
  --  Show that `V ⊆ closure (f '' A)`
  ------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (f '' A) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `w ∈ closure A`
    have hw_clA : w ∈ closure (A : Set X) := by
      -- `U ⊆ closure A`
      have hU_subset : (U : Set X) ⊆ closure (A : Set X) := by
        dsimp [U]
        exact interior_subset
      exact hU_subset hwU
    -- Use continuity to send closures
    have : f w ∈ closure (f '' A) := by
      apply (mem_closure_iff).2
      intro W hW_open hfwinW
      -- Preimage of `W`
      have h_preopen : IsOpen (f ⁻¹' W) := hW_open.preimage hcont
      have hw_pre : w ∈ f ⁻¹' W := by
        simpa using hfwinW
      rcases (mem_closure_iff).1 hw_clA _ h_preopen hw_pre with
        ⟨u, ⟨hu_pre, huA⟩⟩
      refine ⟨f u, ?_⟩
      have hfuW : f u ∈ W := by
        simpa using hu_pre
      have hfuA : f u ∈ f '' A := ⟨u, huA, rfl⟩
      exact And.intro hfuW hfuA
    simpa using this
  ------------------------------------------------------------------
  --  Since `V` is open, it is contained in the interior of the closure.
  ------------------------------------------------------------------
  have hV_subset_int : (V : Set Y) ⊆ interior (closure (f '' A)) :=
    interior_maximal hV_subset hV_open
  exact hV_subset_int hyV