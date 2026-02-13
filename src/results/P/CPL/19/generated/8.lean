

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  -- Apply the lemma for open sets.
  exact P2_of_open (X := X) (A := Aᶜ) hOpen

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P3 A → P3 (e '' A) := by
  intro hP3
  intro y hy
  -- pick a preimage of `y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of the closure of `A`
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  ------------------------------------------------------------------
  -- Define the open neighbourhood on `Y`
  ------------------------------------------------------------------
  set U : Set Y := e.symm ⁻¹' interior (closure A) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using (isOpen_interior).preimage e.symm.continuous
  -- `e x` lies in `U`
  have hxU : (e x) ∈ U := by
    change e.symm (e x) ∈ interior (closure A) at *
    simpa [e.symm_apply_apply] using hx_int
  ------------------------------------------------------------------
  -- Show `U ⊆ closure (e '' A)`
  ------------------------------------------------------------------
  have hU_subset : U ⊆ closure (e '' A) := by
    intro z hzU
    -- Let `u` be the preimage of `z`
    have hu_int : e.symm z ∈ interior (closure A) := by
      simpa [hU_def] using hzU
    have hu_cl : e.symm z ∈ closure A :=
      interior_subset hu_int
    -- Show `z ∈ closure (e '' A)`
    have hz_closure : z ∈ closure (e '' A) := by
      -- use the neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- Preimage of `V` under `e`
      have hWopen : IsOpen (e ⁻¹' V) :=
        hVopen.preimage e.continuous
      have huW : e.symm z ∈ e ⁻¹' V := by
        change e (e.symm z) ∈ V
        simpa using hzV
      -- Intersect with `A`
      have h_nonempty :
          ((e ⁻¹' V) ∩ A).Nonempty :=
        (mem_closure_iff).1 hu_cl (e ⁻¹' V) hWopen huW
      rcases h_nonempty with ⟨w, hwW, hwA⟩
      -- Map this point with `e`
      have hwV : e w ∈ V := by
        -- `w ∈ e ⁻¹' V` gives `e w ∈ V`
        simpa [Set.mem_preimage] using hwW
      have hw_img : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact ⟨e w, hwV, hw_img⟩
    exact hz_closure
  ------------------------------------------------------------------
  -- Conclude: `e x` is in the interior of the closure
  ------------------------------------------------------------------
  have hU_interior :
      U ⊆ interior (closure (e '' A)) := by
    apply interior_maximal
    · exact hU_subset
    · exact hU_open
  exact hU_interior hxU

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` enjoys the `P2` property
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  ------------------------------------------------------------------
  -- An open neighbourhood of `e x`
  ------------------------------------------------------------------
  set U : Set Y := e.symm ⁻¹' interior (closure (interior A)) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using
      (isOpen_interior).preimage e.symm.continuous
  have hxU : (e x) ∈ U := by
    have : e.symm (e x) ∈ interior (closure (interior A)) := by
      simpa [e.symm_apply_apply] using hx_int
    simpa [hU_def] using this
  ------------------------------------------------------------------
  -- Show that `U ⊆ closure (interior (e '' A))`
  ------------------------------------------------------------------
  have hU_subset : U ⊆ closure (interior (e '' A)) := by
    intro z hzU
    have hz_int : e.symm z ∈ interior (closure (interior A)) := by
      simpa [hU_def] using hzU
    have hz_cl : e.symm z ∈ closure (interior A) :=
      interior_subset hz_int
    -- Use the neighbourhood characterisation of the closure
    have hz_closure : z ∈ closure (interior (e '' A)) := by
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- Preimage of `V`
      have hWopen : IsOpen (e ⁻¹' V) :=
        hVopen.preimage e.continuous
      have hzW : e.symm z ∈ e ⁻¹' V := by
        change e (e.symm z) ∈ V
        simpa using hzV
      -- Intersect with `interior A`
      have h_nonempty :
          ((e ⁻¹' V) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hz_cl (e ⁻¹' V) hWopen hzW
      rcases h_nonempty with ⟨w, hwW, hw_intA⟩
      ----------------------------------------------------------------
      -- `e w` will lie in `V ∩ interior (e '' A)`
      ----------------------------------------------------------------
      have hwV : e w ∈ V := by
        have : w ∈ e ⁻¹' V := hwW
        simpa [Set.mem_preimage] using this
      -- Build an open set in `e '' A` that contains `e w`
      let S : Set Y := (e.symm) ⁻¹' interior A
      have hS_open : IsOpen S :=
        (isOpen_interior).preimage e.symm.continuous
      have hS_sub : (S : Set Y) ⊆ e '' A := by
        intro y hyS
        have hy_int : e.symm y ∈ interior A := hyS
        have hyA : e.symm y ∈ A := interior_subset hy_int
        exact ⟨e.symm y, hyA, by simp⟩
      have hS_to_int : (S : Set Y) ⊆ interior (e '' A) := by
        apply interior_maximal
        · exact hS_sub
        · exact hS_open
      have h_e_w_S : e w ∈ S := by
        change e.symm (e w) ∈ interior A
        simpa [e.symm_apply_apply] using hw_intA
      have hw_intEA : e w ∈ interior (e '' A) :=
        hS_to_int h_e_w_S
      exact ⟨e w, hwV, hw_intEA⟩
    exact hz_closure
  ------------------------------------------------------------------
  -- `U` is an open subset of `closure (interior (e '' A))`
  ------------------------------------------------------------------
  have hU_interior :
      U ⊆ interior (closure (interior (e '' A))) := by
    apply interior_maximal
    · exact hU_subset
    · exact hU_open
  exact hU_interior hxU

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 A → P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the `P1` property for `x`
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- show `e x` lies in the closure of `e '' interior A`
  have hx_closure : (e x) ∈ closure (e '' interior A) := by
    apply (mem_closure_iff).2
    intro V hVopen hVmem
    -- consider the preimage of `V` under `e`
    have hWopen : IsOpen (e ⁻¹' V) := hVopen.preimage e.continuous
    have hxW : x ∈ e ⁻¹' V := by
      change e x ∈ V at hVmem
      simpa using hVmem
    -- use that `x` is in the closure of `interior A`
    have h_nonempty :=
      (mem_closure_iff).1 hx_cl (e ⁻¹' V) hWopen hxW
    rcases h_nonempty with ⟨w, hwW, hwIntA⟩
    -- map the witness with `e`
    have hwV : e w ∈ V := by
      have : w ∈ e ⁻¹' V := hwW
      simpa [Set.mem_preimage] using this
    have hw_img : e w ∈ e '' interior A := ⟨w, hwIntA, rfl⟩
    exact ⟨e w, hwV, hw_img⟩
  -- `e '' interior A` is an open subset of `e '' A`, hence contained in its interior
  have h_subset_int : (e '' interior A) ⊆ interior (e '' A) := by
    apply interior_maximal
    · intro z hz
      rcases hz with ⟨w, hwIntA, rfl⟩
      exact ⟨w, interior_subset hwIntA, rfl⟩
    ·
      -- prove `e '' interior A` is open
      have hOpen : IsOpen (e '' interior A) := by
        -- express it as the preimage of an open set under `e.symm`
        have h_eq : (e '' interior A) = e.symm ⁻¹' interior A := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨w, hwIntA, rfl⟩
            change e.symm (e w) ∈ interior A
            simpa [e.symm_apply_apply] using hwIntA
          · intro hz
            have : e.symm z ∈ interior A := hz
            exact ⟨e.symm z, this, by simp⟩
        have hOpen_pre : IsOpen (e.symm ⁻¹' interior A) :=
          (isOpen_interior).preimage e.symm.continuous
        simpa [h_eq] using hOpen_pre
      exact hOpen
  -- taking closures preserves inclusions
  have h_closure_sub :
      closure (e '' interior A) ⊆ closure (interior (e '' A)) :=
    closure_mono h_subset_int
  exact h_closure_sub hx_closure

theorem P1_iff_P2_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) (h_dense : closure A = Set.univ) : P1 A ↔ P2 A := by
  -- Use the density hypothesis just to avoid an unused-argument warning.
  have _ := h_dense
  -- For open sets we already know `P1 A ↔ P3 A` and `P2 A ↔ P3 A`.
  have hP1_P3 : P1 A ↔ P3 A := P1_iff_P3_of_open (X := X) (A := A) hA
  have hP2_P3 : P2 A ↔ P3 A := P2_iff_P3_of_open (X := X) (A := A) hA
  -- Transitivity of `↔` gives the desired equivalence.
  simpa using hP1_P3.trans hP2_P3.symm

theorem P2_subset_P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P1 B → P1 (A ∪ B) := by
  intro hP2 hP1
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
      -- `interior (closure (interior A)) ⊆ closure (interior A)`
      have h1 : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      -- `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h2 : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      -- hence the required inclusion
      have hsubset : interior (closure (interior A)) ⊆
          closure (interior (A ∪ B)) := Set.Subset.trans h1 h2
      exact hsubset hx_int
  | inr hxB =>
      -- `x ∈ B`
      have hx_cl : x ∈ closure (interior B) := hP1 hxB
      -- `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact hsubset hx_cl

theorem P1_fixedpoint_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = A → P1 A := by
  intro h_eq
  intro x hx
  simpa [h_eq] using hx