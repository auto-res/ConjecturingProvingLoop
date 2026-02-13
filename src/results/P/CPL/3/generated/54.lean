

theorem P1_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  rcases hp with ⟨_, hB⟩
  have hFalse : False := by
    simpa [Set.mem_empty_iff_false] using hB
  exact hFalse.elim

theorem P2_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  have hFalse : False := by
    rcases hp with ⟨_, hB⟩
    simpa [Set.mem_empty_iff_false] using hB
  exact hFalse.elim

theorem P3_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  rcases hp with ⟨_, hY⟩
  cases hY

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  intro y hy
  -- 1.  Find a preimage point `x : X` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- 2.  Apply `P2` for `A`.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- 3.  Transport the membership with the homeomorphism `e`.
  have h₁ : e x ∈ (⇑e) '' interior (closure (interior A)) :=
    ⟨x, hx_int, rfl⟩
  -- 4.  Use `e.image_interior` to rewrite.
  have h₂ : e x ∈ interior ((⇑e) '' closure (interior A)) := by
    have h_eq := e.image_interior (s := closure (interior A))
    simpa [h_eq] using h₁
  -- 5.  Use `e.image_closure` to push the `closure` through the image.
  have h₃ : e x ∈ interior (closure ((⇑e) '' interior A)) := by
    have h_eq := e.image_closure (s := interior A)
    simpa [h_eq] using h₂
  -- 6.  One more use of `e.image_interior` to obtain the desired set.
  have h₄ : e x ∈ interior (closure (interior ((⇑e) '' A))) := by
    have h_eq := e.image_interior (s := A)
    simpa [h_eq] using h₃
  simpa using h₄

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  simpa [h_open.interior_eq] using hx_closure