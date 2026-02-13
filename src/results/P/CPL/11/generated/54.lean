

theorem P3_closed_complement : ∀ {X : Type*} [TopologicalSpace X] {A : Set X}, IsClosed A → P3 (Aᶜ) := by
  intro X _ A hA_closed
  have h_open : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact P3_of_open (A := Aᶜ) h_open

theorem P3_covering : ∀ {X : Type*} [TopologicalSpace X] {A : Set X} {ι : Sort*} {U : ι → Set X}, (∀ i, IsOpen (U i)) → (∀ i, A ⊆ U i) → (⋂ i, U i) ⊆ interior (closure A) → P3 A := by
  intro X _topX A ι U hUopen hAsub hInter x hxA
  have hxInter : x ∈ ⋂ i, U i := by
    apply Set.mem_iInter.2
    intro i
    exact hAsub i hxA
  exact hInter hxInter

theorem P2_homeomorph_iff : ∀ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X}, P2 A ↔ P2 (e '' A) := by
  intro X Y _ _ e A
  constructor
  · intro hA
    exact P2_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    -- Transport the property back along `e.symm`.
    have h : P2 (e.symm '' (e '' A)) :=
      P2_image_homeomorph (e := e.symm) (A := (e '' A)) hImg
    -- Identify the transported set with `A`.
    have hEq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h