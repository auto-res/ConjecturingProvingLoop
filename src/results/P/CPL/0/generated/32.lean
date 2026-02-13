

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A → P1 (f '' A) := by
  intro hP1
  intro y hy
  -- pick a preimage point `x : X` with `f x = y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the required closure
  have hx_cl : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
  -- map this membership with `f`
  have h_mem_img : (f x : Y) ∈ f '' closure (interior (A : Set X)) :=
    ⟨x, hx_cl, rfl⟩
  -- `f` sends closures to closures
  have h_img_eq :
      f '' closure (interior (A : Set X)) =
        closure (f '' interior (A : Set X)) := by
    simpa using f.image_closure (s := interior (A : Set X))
  have h2 : (f x : Y) ∈ closure (f '' interior (A : Set X)) := by
    simpa [h_img_eq] using h_mem_img
  -- `f` sends interiors to interiors
  have h_int_eq :
      f '' interior (A : Set X) = interior (f '' A) := by
    simpa using f.image_interior (s := A)
  -- rewrite and conclude
  have : (f x : Y) ∈ closure (interior (f '' A)) := by
    simpa [h_int_eq] using h2
  exact this

theorem exists_dense_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : (∃ B, Dense B ∧ B ⊆ A) → ∃ B, B ⊆ A ∧ P1 B := by
  intro _
  exact ⟨(∅ : Set X), Set.empty_subset _, P1_empty⟩

theorem exists_closed_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P2 C := by
  refine ⟨(Set.univ : Set X), Set.subset_univ A, isClosed_univ, ?_⟩
  exact P2_univ