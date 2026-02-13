

theorem P1_empty_iff {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  simpa using (iff_true_intro (P1_empty (X := X)))

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of `closure A`.
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Apply `e` to get a membership in the image.
  have h1 : e x ∈ (⇑e) '' interior (closure A) := ⟨x, hx_int, rfl⟩
  -- Use `e.image_interior` to rewrite.
  have h2 : e x ∈ interior ((⇑e) '' closure A) := by
    have h_eq := e.image_interior (s := closure A)
    simpa [h_eq] using h1
  -- Use `e.image_closure` to rewrite once more.
  have h3 : e x ∈ interior (closure ((⇑e) '' A)) := by
    have h_eq := e.image_closure (s := A)
    simpa [h_eq] using h2
  simpa using h3

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using P1_prod hA h_univ

theorem P2_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using P2_prod hA h_univ

theorem P3_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using P3_prod hA h_univ

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P2 A ↔ P3 A := by
  have hP1 : P1 A := P1_open h_open
  have h_equiv := (P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact (h_equiv.1 hP2).2
  · intro hP3
    exact h_equiv.2 ⟨hP1, hP3⟩

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  exact (P2_subset_P3 (A := A)) (P2_subsingleton (A := A))