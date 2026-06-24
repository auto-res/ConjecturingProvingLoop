

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_interior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact subset_trans hP2 h_interior

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hA hxA
      have h_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure A ⊆ closure (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono this
        exact interior_mono h_closure
      exact h_mono hx_intA
  | inr hxB =>
      have hx_intB : x ∈ interior (closure B) := hB hxB
      have h_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure B ⊆ closure (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono this
        exact interior_mono h_closure
      exact h_mono hx_intB

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply le_antisymm
    · exact closure_mono (interior_subset : (interior A) ⊆ A)
    ·
      have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using this
  · intro h_eq
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem P2_empty (X : Type*) [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ (X : Type*) [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : Homeomorph X Y) {A : Set X} : P1 A → P1 (h '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have : h x ∈ closure (interior (h '' A)) := by
    apply (mem_closure_iff).2
    intro V hV_open hxV
    have hU_open : IsOpen (h ⁻¹' V) := hV_open.preimage h.continuous
    have hxU : x ∈ h ⁻¹' V := by
      simpa [Set.mem_preimage] using hxV
    have h_nonempty : ((h ⁻¹' V) ∩ interior A).Nonempty := by
      have := (mem_closure_iff).1 hx_cl (h ⁻¹' V) hU_open hxU
      simpa [Set.inter_comm] using this
    rcases h_nonempty with ⟨z, hzU, hzInt⟩
    have hzV : h z ∈ V := by
      have : z ∈ h ⁻¹' V := hzU
      simpa [Set.mem_preimage] using this
    have h_mem_int : h z ∈ interior (h '' A) := by
      have hzO : h z ∈ h '' interior A := ⟨z, hzInt, rfl⟩
      have hO_open : IsOpen (h '' interior A) := by
        have h_eq : (h '' interior A) = (fun y : _ => h.symm y) ⁻¹' interior A := by
          ext y
          constructor
          · rintro ⟨u, hu, rfl⟩
            simpa using hu
          · intro hy
            exact ⟨h.symm y, hy, by simp⟩
        have : IsOpen ((fun y : _ => h.symm y) ⁻¹' interior A) :=
          (isOpen_interior).preimage h.symm.continuous
        simpa [h_eq] using this
      have hO_subset : (h '' interior A) ⊆ h '' A := by
        rintro _ ⟨u, huInt, rfl⟩
        exact ⟨u, interior_subset huInt, rfl⟩
      have h_subset_int : (h '' interior A) ⊆ interior (h '' A) :=
        interior_maximal hO_subset hO_open
      exact h_subset_int hzO
    exact ⟨h z, hzV, h_mem_int⟩
  simpa using this