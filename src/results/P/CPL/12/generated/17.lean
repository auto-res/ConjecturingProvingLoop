

theorem P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 (Aᶜ) := by
  intro hClosed
  exact P3_of_P2 (P2_of_closed_complement hClosed)

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e ⁻¹' B) := by
  intro hP1
  intro x hx
  -- `hx` gives `e x ∈ B`
  have hxB : (e x : Y) ∈ B := hx
  -- Hence `e x ∈ closure (interior B)`
  have h_closure : (e x : Y) ∈ closure (interior (B : Set Y)) := hP1 hxB
  ------------------------------------------------------------------
  -- Goal: `x ∈ closure (interior (e ⁻¹' B))`
  -- First show: `x ∈ closure (e ⁻¹' interior B)`
  ------------------------------------------------------------------
  have hx_closure_pre : (x : X) ∈ closure (e ⁻¹' interior (B : Set Y)) := by
    -- use the neighbourhood‐characterisation of closure
    apply (mem_closure_iff).2
    intro U hU hxU
    -- consider the image `e '' U`
    have hx_image : (e x : Y) ∈ e '' U := ⟨x, hxU, rfl⟩
    -- `e '' U` is open
    have h_open_image : IsOpen (e '' U) := by
      -- rewrite `e '' U` as a preimage of `U` under `e.symm`
      have h_eq : (e '' U : Set Y) = (fun y : Y => e.symm y) ⁻¹' U := by
        ext y
        constructor
        · rintro ⟨z, hzU, rfl⟩
          simpa using hzU
        · intro hy
          exact ⟨e.symm y, hy, by simp⟩
      have h_pre : IsOpen ((fun y : Y => e.symm y) ⁻¹' U) :=
        hU.preimage e.symm.continuous
      simpa [h_eq] using h_pre
    -- the closure condition yields a point in the intersection
    have h_nonempty :
        ((interior (B : Set Y)) ∩ (e '' U)).Nonempty := by
      -- use `mem_closure_iff` for `e x`
      have h := (mem_closure_iff).1 h_closure
      -- the intersection in `h` is `(e '' U) ∩ interior B`
      simpa [Set.inter_comm] using h (e '' U) h_open_image hx_image
    rcases h_nonempty with ⟨y, hy_intB, hy_image⟩
    rcases hy_image with ⟨z, hzU, hy_eq⟩
    -- `z ∈ U` and `e z ∈ interior B`
    have hz_pre : (z : X) ∈ e ⁻¹' interior (B : Set Y) := by
      have : (e z : Y) ∈ interior (B : Set Y) := by
        simpa [hy_eq] using hy_intB
      simpa using this
    -- hence `z ∈ U ∩ e ⁻¹' interior B`
    exact ⟨z, And.intro hzU hz_pre⟩
  ------------------------------------------------------------------
  -- `e ⁻¹' interior B ⊆ interior (e ⁻¹' B)` (open‐set maximality)
  ------------------------------------------------------------------
  have h_open_pre : IsOpen (e ⁻¹' interior (B : Set Y)) :=
    (isOpen_interior).preimage e.continuous
  have h_subset_pre :
      (e ⁻¹' interior (B : Set Y) : Set X) ⊆ e ⁻¹' B := by
    intro y hy
    exact (interior_subset : interior (B : Set Y) ⊆ B) hy
  have h_to_int :
      (e ⁻¹' interior (B : Set Y) : Set X) ⊆ interior (e ⁻¹' B) :=
    interior_maximal h_subset_pre h_open_pre
  have h_closure_mono :
      closure (e ⁻¹' interior (B : Set Y)) ⊆ closure (interior (e ⁻¹' B)) :=
    closure_mono h_to_int
  ------------------------------------------------------------------
  -- conclude
  ------------------------------------------------------------------
  exact h_closure_mono hx_closure_pre

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  -- Pick a preimage point `x : X` with `y = e x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the P2–condition
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  ----------------------------------------------------------------
  -- An auxiliary open set
  ----------------------------------------------------------------
  set S : Set X := interior (closure (interior (A : Set X))) with hSdef
  have hS_open : IsOpen S := by
    simpa [hSdef] using
      (isOpen_interior :
        IsOpen (interior (closure (interior (A : Set X)))))
  have hxS : x ∈ S := by
    simpa [hSdef] using hx
  ----------------------------------------------------------------
  -- The image `e '' S` is open
  ----------------------------------------------------------------
  have hImgOpen : IsOpen (e '' S) := by
    -- Express it as a preimage under the continuous map `e.symm`
    have hEq : (e '' S : Set Y) = (fun y : Y => e.symm y) ⁻¹' S := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨w, hwS, rfl⟩
        simp [hwS]
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
    simpa [hEq] using hS_open.preimage e.symm.continuous
  ----------------------------------------------------------------
  -- Inclusion:  `e '' S ⊆ closure (interior (e '' A))`
  ----------------------------------------------------------------
  have hImgSub :
      (e '' S : Set Y) ⊆ closure (interior (e '' (A : Set X))) := by
    intro z hz
    rcases hz with ⟨w, hwS, rfl⟩
    ----------------------------------------------------------------
    -- 1.  `w ∈ closure (interior A)`
    ----------------------------------------------------------------
    have hw_cl : w ∈ closure (interior (A : Set X)) := by
      -- Since `S ⊆ closure (interior A)`
      have hSsubset :
          (S : Set X) ⊆ closure (interior (A : Set X)) := by
        intro u hu
        -- `u ∈ interior (closure (interior A))`
        have huInt : u ∈
            interior (closure (interior (A : Set X))) := by
          simpa [hSdef] using hu
        -- hence in the closure
        exact (interior_subset : _ ) huInt
      exact hSsubset hwS
    ----------------------------------------------------------------
    -- 2.  `e w ∈ closure (e '' interior A)`
    ----------------------------------------------------------------
    have h_mem1 : (e w : Y) ∈ closure (e '' interior (A : Set X)) := by
      -- First land in `e '' closure (interior A)`
      have : (e w : Y) ∈ e '' closure (interior (A : Set X)) :=
        ⟨w, hw_cl, rfl⟩
      -- Then rewrite with `image_closure`
      have hEq :
          (e '' closure (interior (A : Set X))) =
            closure (e '' interior (A : Set X)) := by
        simpa using e.image_closure (interior (A : Set X))
      simpa [hEq] using this
    ----------------------------------------------------------------
    -- 3.  `closure (e '' interior A) ⊆ closure (interior (e '' A))`
    ----------------------------------------------------------------
    have hSubsetEA :
        (e '' interior (A : Set X) : Set Y) ⊆
          interior (e '' (A : Set X)) := by
      -- `e '' interior A` is open
      have hOpen_eInt : IsOpen (e '' interior (A : Set X)) := by
        -- Again use expression as a preimage
        have hEq2 :
            (e '' interior (A : Set X) : Set Y) =
              (fun y : Y => e.symm y) ⁻¹' interior (A : Set X) := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨u, huInt, rfl⟩
            simp [huInt]
          · intro hy
            exact ⟨e.symm y, hy, by simp⟩
        simpa [hEq2] using isOpen_interior.preimage e.symm.continuous
      -- and is contained in `e '' A`
      have hSub : (e '' interior (A : Set X) : Set Y) ⊆ e '' (A : Set X) := by
        intro v hv
        rcases hv with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      -- apply `interior_maximal`
      exact interior_maximal hSub hOpen_eInt
    have h_closure_subset :
        closure (e '' interior (A : Set X)) ⊆
          closure (interior (e '' (A : Set X))) :=
      closure_mono hSubsetEA
    exact h_closure_subset h_mem1
  ----------------------------------------------------------------
  -- 4.  Maximality of the interior
  ----------------------------------------------------------------
  have hIncl :
      (e '' S : Set Y) ⊆
        interior (closure (interior (e '' (A : Set X)))) :=
    interior_maximal hImgSub hImgOpen
  ----------------------------------------------------------------
  -- 5.  Conclude for the original point
  ----------------------------------------------------------------
  exact hIncl ⟨x, hxS, rfl⟩