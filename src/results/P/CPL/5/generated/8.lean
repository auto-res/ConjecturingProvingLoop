

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (e '' A) := by
  classical
  constructor
  · intro hP2
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    -- step 1 : transport through `e`
    have hx₁ : e x ∈ e '' interior (closure (interior A)) := ⟨x, hx, rfl⟩
    -- step 2 : rewrite with `image_interior`
    have hx₂ : e x ∈ interior (e '' closure (interior A)) := by
      simpa [e.image_interior (s := closure (interior A))] using hx₁
    -- step 3 : rewrite with `image_closure`
    have hx₃ : e x ∈ interior (closure (e '' interior A)) := by
      simpa [e.image_closure (s := interior A)] using hx₂
    -- step 4 : rewrite once more with `image_interior`
    have hx₄ : e x ∈ interior (closure (interior (e '' A))) := by
      simpa [e.image_interior (s := A)] using hx₃
    exact hx₄
  · intro hP2'
    intro x hxA
    -- image point
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    -- apply hypothesis on the image
    have hy' : e x ∈ interior (closure (interior (e '' A))) := hP2' hy
    -- transport back with `e.symm`
    have hx₁ : x ∈ e.symm '' interior (closure (interior (e '' A))) := by
      exact ⟨e x, hy', by simp⟩
    -- use `image_interior` for `e.symm`
    have hx₂ : x ∈ interior (e.symm '' closure (interior (e '' A))) := by
      simpa [e.symm.image_interior (s := closure (interior (e '' A)))] using hx₁
    -- use `image_closure` for `e.symm`
    have hx₃ : x ∈ interior (closure (e.symm '' interior (e '' A))) := by
      simpa [e.symm.image_closure (s := interior (e '' A))] using hx₂
    -- identify `e.symm '' interior (e '' A)` with `interior A`
    -- first, raw images
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have h_eq : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [h_eq] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    have hint : e.symm '' interior (e '' A) = interior A := by
      have h := e.symm.image_interior (s := e '' A)
      simpa [h_image] using h
    have hx_final : x ∈ interior (closure (interior A)) := by
      simpa [hint] using hx₃
    exact hx_final

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (e '' A) := by
  classical
  constructor
  · intro hP3
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure A) := hP3 hxA
    have hx₁ : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
    have hx₂ : e x ∈ interior (e '' closure A) := by
      simpa [e.image_interior (s := closure A)] using hx₁
    have hx₃ : e x ∈ interior (closure (e '' A)) := by
      simpa [e.image_closure (s := A)] using hx₂
    exact hx₃
  · intro hP3'
    intro x hxA
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    have hy' : e x ∈ interior (closure (e '' A)) := hP3' hy
    have hx₁ : x ∈ e.symm '' interior (closure (e '' A)) := by
      exact ⟨e x, hy', by simp⟩
    have hx₂ : x ∈ interior (e.symm '' closure (e '' A)) := by
      simpa [e.symm.image_interior (s := closure (e '' A))] using hx₁
    have hx₃ : x ∈ interior (closure (e.symm '' (e '' A))) := by
      simpa [e.symm.image_closure (s := e '' A)] using hx₂
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have h_eq : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [h_eq] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    simpa [h_image] using hx₃

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (e '' A) := by
  classical
  constructor
  · intro hP1
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ closure (interior A) := hP1 hxA
    have hx₁ : e x ∈ e '' closure (interior A) := ⟨x, hx, rfl⟩
    have hx₂ : e x ∈ closure (e '' interior A) := by
      simpa [e.image_closure (s := interior A)] using hx₁
    have hx₃ : e x ∈ closure (interior (e '' A)) := by
      simpa [e.image_interior (s := A)] using hx₂
    exact hx₃
  · intro hP1'
    intro x hxA
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    have hy' : e x ∈ closure (interior (e '' A)) := hP1' hy
    have hx₁ : x ∈ e.symm '' closure (interior (e '' A)) := ⟨e x, hy', by simp⟩
    have hx₂ : x ∈ closure (e.symm '' interior (e '' A)) := by
      simpa [e.symm.image_closure (s := interior (e '' A))] using hx₁
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [this] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    have hint : e.symm '' interior (e '' A) = interior A := by
      have h := e.symm.image_interior (s := e '' A)
      simpa [h_image] using h
    have hx_final : x ∈ closure (interior A) := by
      simpa [hint] using hx₂
    exact hx_final

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact P3_of_P2 (A := interior A) P2_interior